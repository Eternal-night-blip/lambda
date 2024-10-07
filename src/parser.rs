use std::{fmt::Display, process::exit};

use crate::scanner::{
    Token::{self, *},
    TokenWithContext,
};

#[derive(PartialEq, Debug)]
pub struct AST {
    pub children: Vec<Stmt>,
}

#[derive(PartialEq, Debug)]
pub enum Stmt {
    Definition(DefinitionExpr),
    Application(ApplicationExpr),
}

#[derive(PartialEq, Debug)]
pub struct DefinitionExpr {
    pub name: String,
    pub func_expr: FunctionExpr,
}

#[derive(PartialEq, Clone, Debug)]
pub struct FunctionExpr {
    pub parameter: String,
    pub body: Box<Expr>,
}

#[derive(PartialEq, Clone, Debug)]
pub struct ApplicationExpr {
    pub func_expr: Box<Expr>,
    pub argu_expr: Box<Expr>,
}

#[derive(PartialEq, Clone, Debug)]
pub enum Expr {
    Literal(String),
    Function(FunctionExpr),
    Application(ApplicationExpr),
}

#[derive(Debug)]
enum GrammarError {
    LiteralError(String),
    FunctionError(String),
    ApplicationError(String),
    DefinitionError(String),
    ExpressionError(String),
    StatementError(String),
}

impl Display for GrammarError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GrammarError::LiteralError(s) => write!(f, "{s}"),
            GrammarError::FunctionError(s) => write!(f, "{s}"),
            GrammarError::ApplicationError(s) => write!(f, "{s}"),
            GrammarError::DefinitionError(s) => write!(f, "{s}"),
            GrammarError::ExpressionError(s) => write!(f, "{s}"),
            GrammarError::StatementError(s) => write!(f, "{s}"),
        }
    }
}

/*
 * program := (statement;)* EOF
 * 注意';'仅起到分隔statement的作用
 */
pub fn parse(tokens: &mut Vec<TokenWithContext>) -> AST {
    let mut ast = AST {
        children: Vec::new(),
    };

    trim(tokens);

    //根据';'划分statement
    let mut result: Vec<Vec<TokenWithContext>> = tokens
        .split(|token_with_context| token_with_context.token == Semicolon)
        .map(|stmt| stmt.to_vec())
        .collect();
    match result.pop() {
        None => {
            println!("没有EOF");
            exit(0)
        }
        Some(mut tokens) => {
            trim(&mut tokens);
            if tokens.is_empty() {
                println!("没有EOF");
                exit(0);
            }

            if tokens.len() == 1 {
                if tokens[0].token != EOF {
                    println!("应该是EOF,而不是{:?}", tokens[0]);
                    exit(0)
                }

                let stmts = result;
                stmts
                    .iter()
                    .for_each(|stmt| match statement(&mut stmt.to_vec()) {
                        Ok(work) => ast.children.push(work),
                        Err(err) => {
                            println!("{err}");
                            exit(0)
                        }
                    });
                return ast;
            }

            match tokens
                .iter()
                .find(|token_with_context| token_with_context.token == EOF)
            {
                None => {
                    println!("没有EOF");
                    exit(0)
                }
                Some(_) => {
                    //确保EOF是最后一个Token
                    let token_with_context = tokens.pop().unwrap();
                    match token_with_context.token {
                        EOF => {
                            let copied = tokens.clone();
                            match statement(&mut tokens) {
                                Ok(_) => {
                                    println!(
                                        "语法错误:在第{}行第{}列,语句:{}后应该跟';'",
                                        token_with_context.line,
                                        token_with_context.column,
                                        tokens_to_string(copied)
                                    );
                                    exit(0)
                                }
                                Err(err) => {
                                    println!("{err}");
                                    exit(0)
                                }
                            }
                        }
                        _ => {
                            println!("EOF不在最后");
                            exit(0)
                        }
                    }
                }
            }
        }
    }
}

/*
 * <statement> := <definition> | <application>
 */
fn statement(stmt: &mut Vec<TokenWithContext>) -> Result<Stmt, GrammarError> {
    trim(stmt);
    match stmt.first() {
        Some(token_with_context) => match token_with_context.token {
            Def => match definition(stmt) {
                Ok(work) => Ok(Stmt::Definition(work)),
                Err(err) => Err(err),
            },
            LeftParenthesis => match application(stmt) {
                Ok(work) => Ok(Stmt::Application(work)),
                Err(err) => Err(err),
            },
            _ => Err(GrammarError::StatementError(format!(
                "在第{}行 ,\"{}\"不是语句,缺少'def'或者'('\n",
                token_with_context.line,
                tokens_to_string(stmt.to_vec())
            ))),
        },
        None => Err(GrammarError::StatementError("空语句\n".to_string())),
    }
}

/*
 * <definition> := def <name> '=' <function>
 * (Whitespace*) Def Whitespace* Literal(name) (Whitespace*) Equal (Whitespace*) Function (Whitespace)*
 * def_stmt不可以为空
 * 返回Stmt::Definition
 */
fn definition(input: &mut Vec<TokenWithContext>) -> Result<DefinitionExpr, GrammarError> {
    trim(input);
    match input[0].token {
        Def => {
            let name: String;
            let err_info_prefix = format!(
                "在第{}行,在定义语句\"{}\"中\n:",
                input[0].line,
                tokens_to_string(input.to_vec())
            );
            input.remove(0); //删除Def
            ltrim(input);
            if input.is_empty() {
                return Err(GrammarError::DefinitionError(
                    err_info_prefix + "仅有def,缺失name,'=',function\n",
                ));
            }

            match input.remove(0).token {
                Literal(value) => {
                    name = value;
                }
                other => {
                    return Err(GrammarError::DefinitionError(format!(
                        "{err_info_prefix}此处应该是name(Literal),但是{other}\n"
                    )))
                }
            }
            ltrim(input);
            if input.is_empty() {
                return Err(GrammarError::DefinitionError(
                    err_info_prefix + "缺失'=',function\n",
                ));
            }

            match input.remove(0).token {
                Equal => {}
                other => {
                    return Err(GrammarError::DefinitionError(format!(
                        "{err_info_prefix}此处应该是Equal,却是{other}\n"
                    )))
                }
            }

            ltrim(input);
            if input.is_empty() {
                return Err(GrammarError::DefinitionError(
                    err_info_prefix + "缺失function\n",
                ));
            }

            match function(input) {
                Ok(work) => Ok(DefinitionExpr {
                    name,
                    func_expr: work,
                }),
                Err(fun_err) => {
                    let fun_err = match fun_err {
                        GrammarError::LiteralError(s) => s,
                        GrammarError::FunctionError(s) => s,
                        GrammarError::ApplicationError(s) => s,
                        GrammarError::DefinitionError(s) => s,
                        GrammarError::ExpressionError(s) => s,
                        GrammarError::StatementError(s) => s,
                    };
                    Err(GrammarError::DefinitionError(err_info_prefix + &fun_err))
                }
            }
        }
        _ => Err(GrammarError::DefinitionError(format!(
            "在第{}行,\"{}\"不是定义语句,其之前缺少'def'\n",
            input[0].line,
            tokens_to_string(input.to_vec())
        ))),
    }
}

/*
 * <application> := '(' <function expression> <argument expression> ')'
 * (Whitespace*) LeftParenthesis (Whitespace*) FunctionExpr Whitespace* ArgumentExpr (Whitespace*) RightParenthesis (Whitespace*)
 * app_stmt不可为空
 */
fn application(input: &mut Vec<TokenWithContext>) -> Result<ApplicationExpr, GrammarError> {
    trim(input);
    match input[0].token {
        LeftParenthesis => {
            let err_info_prefix = format!(
                "在第{}行,在应用语句\"{}\"中:\n",
                input[0].line,
                tokens_to_string(input.to_vec())
            );
            input.remove(0); //删除LeftParenthesis
            ltrim(input);

            if input.is_empty() {
                return Err(GrammarError::ApplicationError(
                    err_info_prefix + "仅有'(',缺失function expression,argument expression,')'\n",
                ));
            }

            let function_expr = func_expr(input);
            let fn_expr;
            match function_expr {
                Ok(expr) => fn_expr = expr,
                Err(fn_err) => {
                    let fn_err = match fn_err {
                        GrammarError::LiteralError(s) => s,
                        GrammarError::FunctionError(s) => s,
                        GrammarError::ApplicationError(s) => s,
                        GrammarError::DefinitionError(s) => s,
                        GrammarError::ExpressionError(s) => s,
                        GrammarError::StatementError(s) => s,
                    };
                    return Err(GrammarError::ApplicationError(
                        err_info_prefix + "function expression:\n" + &fn_err,
                    ));
                }
            }

            ltrim(input);

            if input.is_empty() {
                return Err(GrammarError::ApplicationError(
                    err_info_prefix + "缺失argument expression,')'\n",
                ));
            }

            let argument_expr = argu_expr(input);
            let arg_expr;
            match argument_expr {
                Ok(expr) => arg_expr = expr,
                Err(arg_err) => {
                    let arg_err = match arg_err {
                        GrammarError::LiteralError(s) => s,
                        GrammarError::FunctionError(s) => s,
                        GrammarError::ApplicationError(s) => s,
                        GrammarError::DefinitionError(s) => s,
                        GrammarError::ExpressionError(s) => s,
                        GrammarError::StatementError(s) => s,
                    };
                    return Err(GrammarError::ApplicationError(
                        err_info_prefix + "argument expression:\n" + &arg_err,
                    ));
                }
            }

            ltrim(input);

            if input.is_empty() {
                return Err(GrammarError::ApplicationError(
                    err_info_prefix + "缺失')'\n",
                ));
            }

            match input.remove(0).token {
                RightParenthesis => Ok(ApplicationExpr {
                    func_expr: Box::new(fn_expr),
                    argu_expr: Box::new(arg_expr),
                }),
                other => {
                    return Err(GrammarError::ApplicationError(format!(
                        "{err_info_prefix}此处应该是')',却是{other}\n"
                    )))
                }
            }
        }
        _ => Err(GrammarError::ApplicationError(format!(
            "在第{}行,\"{}\"不是应用语句,其之前缺少'('\n",
            input[0].line,
            tokens_to_string(input.to_vec())
        ))),
    }
}

/*
 * <function expression> := <expression>
 */
fn func_expr(input: &mut Vec<TokenWithContext>) -> Result<Expr, GrammarError> {
    expression(input)
}

/*
 * <argument expression> := <expression>
 */
fn argu_expr(input: &mut Vec<TokenWithContext>) -> Result<Expr, GrammarError> {
    expression(input)
}

/*
 * <expression> := <name> | <function> | <application>
 * (White*) Name | Function |Application (Whitespace*)
 */
fn expression(expr: &mut Vec<TokenWithContext>) -> Result<Expr, GrammarError> {
    trim(expr);
    match expr.first() {
        Some(token_with_context) => match token_with_context.token {
            Literal(_) => return literal(expr),

            Lambda => {
                let result = function(expr);
                match result {
                    Ok(work) => Ok(Expr::Function(work)),
                    Err(err) => Err(err),
                }
            }
            LeftParenthesis => {
                let result = application(expr);
                match result {
                    Ok(work) => Ok(Expr::Application(work)),
                    Err(err) => Err(err),
                }
            }
            _ => Err(GrammarError::ExpressionError(format!(
                "在第{}行,\"{}\"不是表达式,缺少'λ'或者'('\n",
                token_with_context.line,
                tokens_to_string(expr.to_vec())
            ))),
        },
        None => Err(GrammarError::ExpressionError("空表达式\n".to_string())),
    }
}

/*
 * <literal> := <name>
 * expr不可以为空
 */
fn literal(expr: &mut Vec<TokenWithContext>) -> Result<Expr, GrammarError> {
    trim(expr);
    match &expr[0].token {
        Literal(name) => {
            let value = name.clone();
            expr.remove(0);
            Ok(Expr::Literal(value))
        }
        _ => Err(GrammarError::LiteralError(format!(
            "在第{}行,第{}列,{}不是变量\n",
            expr[0].line, expr[0].column, expr[0].token
        ))),
    }
}

/*
 * <function> := λ<name>.<body>
 * (Whitespace*) Lambda Literal Dot Body (Whitespace*)
 * expr不可以为空
 */
fn function(input: &mut Vec<TokenWithContext>) -> Result<FunctionExpr, GrammarError> {
    trim(input);
    match input[0].token {
        Lambda => {
            let err_info_prefix = format!(
                "在第{}行,在函数表达式\"{}\"中:\n",
                input[0].line,
                tokens_to_string(input.to_vec())
            );
            input.remove(0); //删除Lambda
            if input.is_empty() {
                return Err(GrammarError::FunctionError(
                    err_info_prefix + "缺失name,'.',body\n",
                ));
            }

            let parameter;
            match input.remove(0).token {
                Literal(name) => parameter = name,
                other => {
                    return Err(GrammarError::FunctionError(format!(
                        "{err_info_prefix}此处应该是name(Literal),却是{other}\n"
                    )))
                }
            }

            if input.is_empty() {
                return Err(GrammarError::FunctionError(
                    err_info_prefix + "缺失'.',body\n",
                ));
            }
            match input.remove(0).token {
                Dot => {}
                other => {
                    return Err(GrammarError::FunctionError(format!(
                        "{err_info_prefix}此处应该是'.',却是{other}\n"
                    )))
                }
            }

            if input.is_empty() {
                return Err(GrammarError::FunctionError(err_info_prefix + "缺失body\n"));
            }

            match body(input) {
                Ok(work) => Ok(FunctionExpr {
                    parameter,
                    body: Box::new(work),
                }),
                Err(body_err) => {
                    let body_err = match body_err {
                        GrammarError::LiteralError(s) => s,
                        GrammarError::FunctionError(s) => s,
                        GrammarError::ApplicationError(s) => s,
                        GrammarError::DefinitionError(s) => s,
                        GrammarError::ExpressionError(s) => s,
                        GrammarError::StatementError(s) => s,
                    };
                    Err(GrammarError::FunctionError(err_info_prefix + &body_err))
                }
            }
        }
        _ => Err(GrammarError::FunctionError(format!(
            "在第{}行,\"{}\"不是函数表达式,其之前缺少'λ'\n",
            input[0].line,
            tokens_to_string(input.to_vec())
        ))),
    }
}

/*
 * <body> := <expression>
 */
fn body(input: &mut Vec<TokenWithContext>) -> Result<Expr, GrammarError> {
    expression(input)
}

/*
 * 去除Token序列左右两侧的Whitespace
 */
fn trim(input: &mut Vec<TokenWithContext>) {
    ltrim(input);
    rtrim(input);
}

/*
 * 去掉Token序列左侧的Whitespace
 */
fn ltrim(input: &mut Vec<TokenWithContext>) {
    while input.len() > 0 && input[0].token == Whitespace {
        input.remove(0);
    }
}

/*
 * 去掉Token序列右侧的Whitespace
 */
fn rtrim(input: &mut Vec<TokenWithContext>) {
    input.reverse();
    ltrim(input);
    input.reverse();
}

/*
 * 将tokens转换成原字符序列方便报错信息
 * 会删除左右两侧不必要的空格
 */
fn tokens_to_string(input: Vec<TokenWithContext>) -> String {
    input
        .iter()
        .map(|token| token_to_string(token.token.clone()))
        .fold("".to_string(), |acc, x| acc + &x)
        .trim()
        .to_string()
}

fn token_to_string(input: Token) -> String {
    match input {
        Lambda => 'λ'.to_string(),
        Literal(x) => x,
        Number(x) => x,
        LeftParenthesis => '('.to_string(),
        RightParenthesis => ')'.to_string(),
        Def => "def".to_string(),
        Equal => '='.to_string(),
        Whitespace => ' '.to_string(),
        Dot => '.'.to_string(),
        Semicolon => ';'.to_string(),
        _ => "".to_string(),
    }
}

#[cfg(test)]
mod parser_tests {
    use crate::{
        parser::{
            application, definition, parse, tokens_to_string, trim, ApplicationExpr,
            DefinitionExpr, Expr, FunctionExpr, GrammarError, Stmt, AST,
        },
        scanner::{
            Token::{self, *},
            TokenWithContext,
        },
    };

    use super::{expression, function, statement};

    #[test]
    fn check_split_stmt() {
        let input = vec![
            Def,
            Literal("identity".to_string()),
            Equal,
            Lambda,
            Literal("x".to_string()),
            Dot,
            Literal("x".to_string()),
            Semicolon,
            LeftParenthesis,
            Lambda,
            Literal("x".to_string()),
            Dot,
            Literal("x".to_string()),
            Whitespace,
            Lambda,
            Literal("x".to_string()),
            Dot,
            Literal("x".to_string()),
            RightParenthesis,
            Semicolon,
            EOF,
        ];
        let result: Vec<Vec<Token>> = input
            .split(|token| *token == Semicolon)
            .map(|stmt| stmt.to_vec())
            .collect();
        assert_eq!(
            result,
            vec![
                vec![
                    Def,
                    Literal("identity".to_string()),
                    Equal,
                    Lambda,
                    Literal("x".to_string()),
                    Dot,
                    Literal("x".to_string())
                ],
                vec![
                    LeftParenthesis,
                    Lambda,
                    Literal("x".to_string()),
                    Dot,
                    Literal("x".to_string()),
                    Whitespace,
                    Lambda,
                    Literal("x".to_string()),
                    Dot,
                    Literal("x".to_string()),
                    RightParenthesis
                ],
                vec![EOF]
            ]
        );
    }

    #[test]
    fn check_trim() {
        let origin = &mut vec![];
        trim(origin);
        assert_eq!(*origin, vec![]);

        let origin = &mut vec![
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 2,
            },
        ];
        trim(origin);
        assert_eq!(
            *origin,
            vec![
                TokenWithContext {
                    token: Lambda,
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: Dot,
                    line: 1,
                    column: 2
                }
            ]
        );

        let origin = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 3,
            },
        ];
        trim(origin);
        assert_eq!(
            *origin,
            vec![
                TokenWithContext {
                    token: Lambda,
                    line: 1,
                    column: 2
                },
                TokenWithContext {
                    token: Dot,
                    line: 1,
                    column: 3
                }
            ]
        );

        let origin = &mut vec![
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 3,
            },
        ];
        trim(origin);
        assert_eq!(
            *origin,
            vec![
                TokenWithContext {
                    token: Lambda,
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: Dot,
                    line: 1,
                    column: 2
                }
            ]
        );

        let origin = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
        ];
        trim(origin);
        assert_eq!(
            *origin,
            vec![
                TokenWithContext {
                    token: Lambda,
                    line: 1,
                    column: 2
                },
                TokenWithContext {
                    token: Dot,
                    line: 1,
                    column: 3
                }
            ]
        );

        let origin = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
        ];
        trim(origin);
        assert_eq!(
            *origin,
            vec![
                TokenWithContext {
                    token: Lambda,
                    line: 1,
                    column: 3
                },
                TokenWithContext {
                    token: Dot,
                    line: 1,
                    column: 4
                }
            ]
        );

        let origin = &mut vec![
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 3,
            },
        ];
        trim(origin);
        assert_eq!(
            *origin,
            vec![
                TokenWithContext {
                    token: Lambda,
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: Whitespace,
                    line: 1,
                    column: 2
                },
                TokenWithContext {
                    token: Dot,
                    line: 1,
                    column: 3
                }
            ]
        );

        let origin = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 7,
            },
        ];
        trim(origin);
        assert_eq!(
            *origin,
            vec![
                TokenWithContext {
                    token: Lambda,
                    line: 1,
                    column: 3
                },
                TokenWithContext {
                    token: Whitespace,
                    line: 1,
                    column: 4
                },
                TokenWithContext {
                    token: Dot,
                    line: 1,
                    column: 5
                }
            ]
        );
    }

    #[test]
    fn check_tokens_to_string() {
        //  def identity =λx.(x x) ;
        let tokens = vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Def,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("identity".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 15,
            },
            TokenWithContext {
                token: Equal,
                line: 1,
                column: 16,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 17,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 18,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 19,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 20,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 21,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 22,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 23,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 24,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 25,
            },
            TokenWithContext {
                token: Semicolon,
                line: 1,
                column: 26,
            },
        ];
        assert_eq!(tokens_to_string(tokens), "def identity =λx.(x x) ;");
    }

    #[test]
    fn check_expression() {
        // name x
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
        ];
        let expr = expression(tokens);
        assert_eq!(expr.unwrap(), Expr::Literal("x".to_string()));

        // function λx.x
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 7,
            },
        ];
        let expr = expression(tokens);
        assert_eq!(
            expr.unwrap(),
            Expr::Function(FunctionExpr {
                parameter: "x".to_string(),
                body: Box::new(Expr::Literal("x".to_string()))
            })
        );

        // application (x x)
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 8,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 9,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 10,
            },
        ];
        let expr = expression(tokens);
        assert_eq!(
            expr.unwrap(),
            Expr::Application(ApplicationExpr {
                func_expr: Box::new(Expr::Literal("x".to_string())),
                argu_expr: Box::new(Expr::Literal("x".to_string()))
            })
        );

        // panic!
        // 不是表达式 .x
        let tokens = &mut vec![
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 3,
            },
        ];
        match expression(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::ExpressionError(err) => {
                    assert_eq!(err, "在第1行,\".x\"不是表达式,缺少'λ'或者'('\n");
                }
                _ => panic!("应该是ExpressionError"),
            },
        }

        //空表达式
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
        ];
        match expression(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::ExpressionError(err) => {
                    assert_eq!(err, "空表达式\n");
                }
                _ => panic!("应该是ExpressionError"),
            },
        }
    }

    #[test]
    fn check_function() {
        // λx.x
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 7,
            },
        ];
        let func_expr = function(tokens);
        assert_eq!(
            func_expr.unwrap(),
            FunctionExpr {
                parameter: "x".to_string(),
                body: Box::new(Expr::Literal("x".to_string()))
            }
        );

        // λx.λy.x
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("y".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 8,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 9,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 10,
            },
        ];
        let func_expr = function(tokens);
        assert_eq!(
            func_expr.unwrap(),
            FunctionExpr {
                parameter: "x".to_string(),
                body: Box::new(Expr::Function(FunctionExpr {
                    parameter: "y".to_string(),
                    body: Box::new(Expr::Literal("x".to_string()))
                }))
            }
        );

        // λx.(x x)
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 8,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 9,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 10,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 11,
            },
        ];
        let func_expr = function(tokens);
        assert_eq!(
            func_expr.unwrap(),
            FunctionExpr {
                parameter: "x".to_string(),
                body: Box::new(Expr::Application(ApplicationExpr {
                    func_expr: Box::new(Expr::Literal("x".to_string())),
                    argu_expr: Box::new(Expr::Literal("x".to_string()))
                }))
            }
        );

        // λx.λy.(x y)
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("y".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 8,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 9,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 10,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 11,
            },
            TokenWithContext {
                token: Literal("y".to_string()),
                line: 1,
                column: 12,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 13,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 14,
            },
        ];
        let func_expr = function(tokens);
        assert_eq!(
            func_expr.unwrap(),
            FunctionExpr {
                parameter: "x".to_string(),
                body: Box::new(Expr::Function(FunctionExpr {
                    parameter: "y".to_string(),
                    body: Box::new(Expr::Application(ApplicationExpr {
                        func_expr: Box::new(Expr::Literal("x".to_string())),
                        argu_expr: Box::new(Expr::Literal("y".to_string()))
                    }))
                }))
            }
        );

        // panic!
        // 不是函数表达式 x.x
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
        ];
        match function(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::FunctionError(err) => {
                    assert_eq!(err, "在第1行,\"x.x\"不是函数表达式,其之前缺少'λ'\n");
                }
                _ => panic!("应该是FunctionError"),
            },
        }

        // 应该是函数表达式,但是
        // λ
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
        ];
        match function(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::FunctionError(err) => {
                    assert_eq!(err, "在第1行,在函数表达式\"λ\"中:\n缺失name,'.',body\n");
                }
                _ => panic!("应该是FunctionError"),
            },
        }

        // λ.
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 5,
            },
        ];
        match function(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::FunctionError(err) => {
                    assert_eq!(
                        err,
                        "在第1行,在函数表达式\"λ.\"中:\n此处应该是name(Literal),却是Dot\n"
                    );
                }
                _ => panic!("应该是FunctionError"),
            },
        }

        // λx
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 5,
            },
        ];
        match function(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::FunctionError(err) => {
                    assert_eq!(err, "在第1行,在函数表达式\"λx\"中:\n缺失'.',body\n");
                }
                _ => panic!("应该是FunctionError"),
            },
        }

        // λx=
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Equal,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
        ];
        match function(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::FunctionError(err) => {
                    assert_eq!(
                        err,
                        "在第1行,在函数表达式\"λx=\"中:\n此处应该是'.',却是Equal\n"
                    );
                }
                _ => panic!("应该是FunctionError"),
            },
        }

        // λx.
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
        ];
        match function(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::FunctionError(err) => {
                    assert_eq!(err, "在第1行,在函数表达式\"λx.\"中:\n缺失body\n");
                }
                _ => panic!("应该是FunctionError"),
            },
        }

        // λx.=
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Equal,
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 8,
            },
        ];
        match function(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::FunctionError(err) => {
                    assert_eq!(
                        err,
                        "在第1行,在函数表达式\"λx. =\"中:\n在第1行,\"=\"不是表达式,缺少'λ'或者'('\n"
                    );
                }
                _ => panic!("应该是FunctionError"),
            },
        }
    }

    #[test]
    fn check_definition() {
        // def identity = λx.x
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Def,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("identity".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 15,
            },
            TokenWithContext {
                token: Equal,
                line: 1,
                column: 16,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 17,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 18,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 19,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 20,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 21,
            },
        ];
        let def_expr = definition(tokens);
        assert_eq!(
            def_expr.unwrap(),
            DefinitionExpr {
                name: "identity".to_string(),
                func_expr: FunctionExpr {
                    parameter: "x".to_string(),
                    body: Box::new(Expr::Literal("x".to_string()))
                }
            }
        );

        // panic!
        // 不是定义语句  identity = λx.x
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Literal("identity".to_string()),
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 11,
            },
            TokenWithContext {
                token: Equal,
                line: 1,
                column: 12,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 13,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 14,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 15,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 16,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 17,
            },
        ];
        match definition(tokens) {
            Ok(_) => {}
            Err(err) => match err {
                GrammarError::DefinitionError(err) => {
                    assert_eq!(
                        err,
                        "在第1行,\"identity =λx.x\"不是定义语句,其之前缺少'def'\n"
                    );
                }
                _ => panic!("应该是DefinitionError"),
            },
        }

        //应该是定义语句,但是
        // def
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Def,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
        ];
        match definition(tokens) {
            Ok(_) => {}
            Err(err) => match err {
                GrammarError::DefinitionError(err) => {
                    assert_eq!(
                        err,
                        "在第1行,在定义语句\"def\"中\n:仅有def,缺失name,'=',function\n"
                    );
                }
                _ => panic!("应该是DefinitionError"),
            },
        }

        // def λ
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Def,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 7,
            },
        ];
        match definition(tokens) {
            Ok(_) => {}
            Err(err) => match err {
                GrammarError::DefinitionError(err) => {
                    assert_eq!(
                        err,
                        "在第1行,在定义语句\"def λ\"中\n:此处应该是name(Literal),但是Lambda\n"
                    );
                }
                _ => panic!("应该是DefinitionError"),
            },
        }

        // def identity
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Def,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("identity".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 8,
            },
        ];
        match definition(tokens) {
            Ok(_) => {}
            Err(err) => match err {
                GrammarError::DefinitionError(err) => {
                    assert_eq!(
                        err,
                        "在第1行,在定义语句\"def identity\"中\n:缺失'=',function\n"
                    );
                }
                _ => panic!("应该是DefinitionError"),
            },
        }

        // def identity .
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Def,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("identity".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 15,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 16,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 17,
            },
        ];
        match definition(tokens) {
            Ok(_) => {}
            Err(err) => match err {
                GrammarError::DefinitionError(err) => {
                    assert_eq!(
                        err,
                        "在第1行,在定义语句\"def identity .\"中\n:此处应该是Equal,却是Dot\n"
                    );
                }
                _ => panic!("应该是DefinitionError"),
            },
        }

        // def identity =
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Def,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("identity".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 15,
            },
            TokenWithContext {
                token: Equal,
                line: 1,
                column: 16,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 17,
            },
        ];
        match definition(tokens) {
            Ok(_) => {}
            Err(err) => match err {
                GrammarError::DefinitionError(err) => {
                    assert_eq!(
                        err,
                        "在第1行,在定义语句\"def identity =\"中\n:缺失function\n"
                    );
                }
                _ => panic!("应该是DefinitionError"),
            },
        }

        // def identity = x
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Def,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("identity".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 15,
            },
            TokenWithContext {
                token: Equal,
                line: 1,
                column: 16,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 17,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 18,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 19,
            },
        ];
        match definition(tokens) {
            Ok(_) => {}
            Err(err) => match err {
                GrammarError::DefinitionError(err) => {
                    assert_eq!(err, "在第1行,在定义语句\"def identity = x\"中\n:在第1行,\"x\"不是函数表达式,其之前缺少'λ'\n");
                }
                _ => panic!("应该是DefinitionError"),
            },
        }
    }

    #[test]
    fn check_application() {
        // 抽象形式 (x y)
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("y".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 8,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 9,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 10,
            },
        ];
        let expr = application(tokens);
        assert_eq!(
            expr.unwrap(),
            ApplicationExpr {
                func_expr: Box::new(Expr::Literal("x".to_string())),
                argu_expr: Box::new(Expr::Literal("y".to_string()))
            }
        );

        // (λx.x y)
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 8,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 9,
            },
            TokenWithContext {
                token: Literal("y".to_string()),
                line: 1,
                column: 10,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 11,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 12,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 13,
            },
        ];
        let expr = application(tokens);
        assert_eq!(
            expr.unwrap(),
            ApplicationExpr {
                func_expr: Box::new(Expr::Function(FunctionExpr {
                    parameter: "x".to_string(),
                    body: Box::new(Expr::Literal("x".to_string()))
                })),
                argu_expr: Box::new(Expr::Literal("y".to_string()))
            }
        );

        // (λx.x λx.x)
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 8,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 9,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 10,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 11,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 12,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 13,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 14,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 15,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 16,
            },
        ];
        let expr = application(tokens);
        assert_eq!(
            expr.unwrap(),
            ApplicationExpr {
                func_expr: Box::new(Expr::Function(FunctionExpr {
                    parameter: "x".to_string(),
                    body: Box::new(Expr::Literal("x".to_string()))
                })),
                argu_expr: Box::new(Expr::Function(FunctionExpr {
                    parameter: "x".to_string(),
                    body: Box::new(Expr::Literal("x".to_string()))
                }))
            }
        );

        // (λx.x λs.(s s))
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 8,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 9,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 10,
            },
            TokenWithContext {
                token: Literal("s".to_string()),
                line: 1,
                column: 11,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 12,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 13,
            },
            TokenWithContext {
                token: Literal("s".to_string()),
                line: 1,
                column: 14,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 15,
            },
            TokenWithContext {
                token: Literal("s".to_string()),
                line: 1,
                column: 16,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 17,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 18,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 19,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 20,
            },
        ];
        let expr = application(tokens);
        assert_eq!(
            expr.unwrap(),
            ApplicationExpr {
                func_expr: Box::new(Expr::Function(FunctionExpr {
                    parameter: "x".to_string(),
                    body: Box::new(Expr::Literal("x".to_string()))
                })),
                argu_expr: Box::new(Expr::Function(FunctionExpr {
                    parameter: "s".to_string(),
                    body: Box::new(Expr::Application(ApplicationExpr {
                        func_expr: Box::new(Expr::Literal("s".to_string())),
                        argu_expr: Box::new(Expr::Literal("s".to_string()))
                    }))
                }))
            }
        );

        // (λs.(s s) λx.x)
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Literal("s".to_string()),
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 8,
            },
            TokenWithContext {
                token: Literal("s".to_string()),
                line: 1,
                column: 9,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 10,
            },
            TokenWithContext {
                token: Literal("s".to_string()),
                line: 1,
                column: 11,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 12,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 13,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 14,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 15,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 16,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 17,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 18,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 19,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 20,
            },
        ];
        let expr = application(tokens);
        assert_eq!(
            expr.unwrap(),
            ApplicationExpr {
                func_expr: Box::new(Expr::Function(FunctionExpr {
                    parameter: "s".to_string(),
                    body: Box::new(Expr::Application(ApplicationExpr {
                        func_expr: Box::new(Expr::Literal("s".to_string())),
                        argu_expr: Box::new(Expr::Literal("s".to_string()))
                    }))
                })),
                argu_expr: Box::new(Expr::Function(FunctionExpr {
                    parameter: "x".to_string(),
                    body: Box::new(Expr::Literal("x".to_string()))
                }))
            }
        );

        //(λs.(s s) λx.(x x))
        //
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Literal("s".to_string()),
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 8,
            },
            TokenWithContext {
                token: Literal("s".to_string()),
                line: 1,
                column: 9,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 10,
            },
            TokenWithContext {
                token: Literal("s".to_string()),
                line: 1,
                column: 11,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 12,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 13,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 14,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 15,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 16,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 17,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 18,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 19,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 20,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 21,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 22,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 23,
            },
        ];
        let expr = application(tokens);
        assert_eq!(
            expr.unwrap(),
            ApplicationExpr {
                func_expr: Box::new(Expr::Function(FunctionExpr {
                    parameter: "s".to_string(),
                    body: Box::new(Expr::Application(ApplicationExpr {
                        func_expr: Box::new(Expr::Literal("s".to_string())),
                        argu_expr: Box::new(Expr::Literal("s".to_string()))
                    }))
                })),
                argu_expr: Box::new(Expr::Function(FunctionExpr {
                    parameter: "x".to_string(),
                    body: Box::new(Expr::Application(ApplicationExpr {
                        func_expr: Box::new(Expr::Literal("x".to_string())),
                        argu_expr: Box::new(Expr::Literal("x".to_string()))
                    }))
                }))
            }
        );

        //panic!
        // 不是应用语句 x y
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Literal("y".to_string()),
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 7,
            },
        ];
        match application(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::ApplicationError(err) => {
                    assert_eq!(err, "在第1行,\"x y\"不是应用语句,其之前缺少'('\n");
                }
                _ => panic!("应该是ApplicationError"),
            },
        }

        //应该是引用语句,但是
        // (
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
        ];
        match application(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::ApplicationError(err) => {
                    assert_eq!(err, "在第1行,在应用语句\"(\"中:\n仅有'(',缺失function expression,argument expression,')'\n");
                }
                _ => panic!("应该是ApplicationError"),
            },
        }

        // ( =
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Equal,
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
        ];
        match application(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::ApplicationError(err) => {
                    assert_eq!(err, "在第1行,在应用语句\"( =\"中:\nfunction expression:\n在第1行,\"=\"不是表达式,缺少'λ'或者'('\n");
                }
                _ => panic!("应该是ApplicationError"),
            },
        }

        // ( x
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
        ];
        match application(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::ApplicationError(err) => {
                    assert_eq!(
                        err,
                        "在第1行,在应用语句\"( x\"中:\n缺失argument expression,')'\n"
                    );
                }
                _ => panic!("应该是ApplicationError"),
            },
        }

        // ( x =
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Equal,
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 8,
            },
        ];
        match application(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::ApplicationError(err) => {
                    assert_eq!(err, "在第1行,在应用语句\"( x =\"中:\nargument expression:\n在第1行,\"=\"不是表达式,缺少'λ'或者'('\n");
                }
                _ => panic!("应该是ApplicationError"),
            },
        }

        // ( x y
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("y".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 8,
            },
        ];
        match application(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::ApplicationError(err) => {
                    assert_eq!(err, "在第1行,在应用语句\"( x y\"中:\n缺失')'\n");
                }
                _ => panic!("应该是ApplicationError"),
            },
        }

        // ( x y .
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("y".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 8,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 9,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 10,
            },
        ];
        match application(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::ApplicationError(err) => {
                    assert_eq!(
                        err,
                        "在第1行,在应用语句\"( x y .\"中:\n此处应该是')',却是Dot\n"
                    );
                }
                _ => panic!("应该是ApplicationError"),
            },
        }
    }

    #[test]
    fn check_statement() {
        // definition statement
        // def identity = λx.x
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Def,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("identity".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 15,
            },
            TokenWithContext {
                token: Equal,
                line: 1,
                column: 16,
            },
            TokenWithContext {
                token: Lambda,
                line: 1,
                column: 17,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 18,
            },
            TokenWithContext {
                token: Dot,
                line: 1,
                column: 19,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 20,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 21,
            },
        ];
        let stmt = statement(tokens);
        assert_eq!(
            stmt.unwrap(),
            Stmt::Definition(DefinitionExpr {
                name: "identity".to_string(),
                func_expr: FunctionExpr {
                    parameter: "x".to_string(),
                    body: Box::new(Expr::Literal("x".to_string()))
                }
            })
        );

        // application statement
        // (x y)
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("y".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 8,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 9,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 10,
            },
        ];
        let stmt = statement(tokens);
        assert_eq!(
            stmt.unwrap(),
            Stmt::Application(ApplicationExpr {
                func_expr: Box::new(Expr::Literal("x".to_string())),
                argu_expr: Box::new(Expr::Literal("y".to_string()))
            })
        );

        //panic!
        // 不是语句 x y
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Literal("y".to_string()),
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 7,
            },
        ];
        match statement(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::StatementError(err) => {
                    assert_eq!(err, "在第1行 ,\"x y\"不是语句,缺少'def'或者'('\n");
                }
                _ => panic!("应该是StatementError"),
            },
        }

        //空语句
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
        ];
        match statement(tokens) {
            Ok(_) => panic!("应该有错误"),
            Err(err) => match err {
                GrammarError::StatementError(err) => {
                    assert_eq!(err, "空语句\n");
                }
                _ => panic!("应该是StatementError"),
            },
        }
    }

    #[test]
    fn check_parse() {
        // (x y ); (x y); EOF
        let tokens = &mut vec![
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 1,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 2,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 3,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 4,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 5,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 6,
            },
            TokenWithContext {
                token: Literal("y".to_string()),
                line: 1,
                column: 7,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 8,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 9,
            },
            TokenWithContext {
                token: Semicolon,
                line: 1,
                column: 10,
            },
            TokenWithContext {
                token: LeftParenthesis,
                line: 1,
                column: 11,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 12,
            },
            TokenWithContext {
                token: Literal("x".to_string()),
                line: 1,
                column: 13,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 14,
            },
            TokenWithContext {
                token: Literal("y".to_string()),
                line: 1,
                column: 15,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 16,
            },
            TokenWithContext {
                token: RightParenthesis,
                line: 1,
                column: 17,
            },
            TokenWithContext {
                token: Semicolon,
                line: 1,
                column: 18,
            },
            TokenWithContext {
                token: Whitespace,
                line: 1,
                column: 19,
            },
            TokenWithContext {
                token: EOF,
                line: 1,
                column: 20,
            },
        ];
        let ast = parse(tokens);
        assert_eq!(
            ast,
            AST {
                children: vec![
                    Stmt::Application(ApplicationExpr {
                        func_expr: Box::new(Expr::Literal("x".to_string())),
                        argu_expr: Box::new(Expr::Literal("y".to_string()))
                    }),
                    Stmt::Application(ApplicationExpr {
                        func_expr: Box::new(Expr::Literal("x".to_string())),
                        argu_expr: Box::new(Expr::Literal("y".to_string()))
                    })
                ]
            }
        );
    }
}
