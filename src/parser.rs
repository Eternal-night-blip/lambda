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

#[derive(Debug, PartialEq)]
pub struct Position {
    pub line: usize,
    pub column: usize,
}

#[derive(Debug, PartialEq)]
pub struct GrammarError {
    pub err_info: String,
    pub start: Position,
    pub end: Position,
}

type ParseResult<'a, Output> = Result<(&'a str, usize, usize, Output), GrammarError>;

trait Parser<'a, Output> {
    fn parse(&self, input: &'a str, line: usize, column: usize) -> ParseResult<'a, Output>;
}

impl<'a, F, Output> Parser<'a, Output> for F
where
    F: Fn(&'a str, usize, usize) -> ParseResult<Output>,
{
    fn parse(&self, input: &'a str, line: usize, column: usize) -> ParseResult<'a, Output> {
        self(input, line, column)
    }
}

/*
 * 将parser计算的结果进行类型转换
 */
fn map<'a, P, F, A, B>(parser: P, converter: F) -> impl Parser<'a, B>
where
    P: Parser<'a, A>,
    F: Fn(A) -> B,
{
    move |input, line, column| {
        parser
            .parse(input, line, column)
            .map(|(next_input, line, column, result)| (next_input, line, column, converter(result)))
    }
}

/*
 * 先让parser1解析,将成功的解析结果传送到parser2,让parser2再解析
 */
fn pair<'a, P1, P2, R1, R2>(parser1: P1, parser2: P2) -> impl Parser<'a, (R1, R2)>
where
    P1: Parser<'a, R1>,
    P2: Parser<'a, R2>,
{
    move |input, line, column| {
        parser1
            .parse(input, line, column)
            .and_then(|(next_input, line, column, result1)| {
                parser2.parse(next_input, line, column).map(
                    |(final_input, line, column, result2)| {
                        (final_input, line, column, (result1, result2))
                    },
                )
            })
    }
}

fn left<'a, P1, P2, R1, R2>(parser1: P1, parser2: P2) -> impl Parser<'a, R1>
where
    P1: Parser<'a, R1>,
    P2: Parser<'a, R2>,
{
    map(pair(parser1, parser2), |(left, _right)| left)
}

fn right<'a, P1, P2, R1, R2>(parser1: P1, parser2: P2) -> impl Parser<'a, R2>
where
    P1: Parser<'a, R1>,
    P2: Parser<'a, R2>,
{
    map(pair(parser1, parser2), |(_left, right)| right)
}

fn zero_or_more<'a, P, A>(parser: P) -> impl Parser<'a, Vec<A>>
where
    P: Parser<'a, A>,
{
    move |mut input, line, column| {
        let mut result = Vec::new();
        let mut current_line = line;
        let mut current_column = column;
        while let Ok((next_input, line, column, next_item)) =
            parser.parse(input, current_line, current_column)
        {
            input = next_input;
            current_line = line;
            current_column = column;
            result.push(next_item);
        }

        Ok((input, current_line, current_column, result))
    }
}

fn one_or_more<'a, P, A>(parser: P) -> impl Parser<'a, Vec<A>>
where
    P: Parser<'a, A>,
{
    move |mut input, line, column| {
        let mut result = Vec::new();
        let mut current_line = line;
        let mut current_column = column;

        match parser.parse(input, current_line, current_column) {
            Ok((next_input, line, column, first_item)) => {
                input = next_input;
                current_line = line;
                current_column = column;
                result.push(first_item);
            }
            Err(err) => return Err(err),
        }

        while let Ok((next_input, line, column, next_item)) =
            parser.parse(input, current_line, current_column)
        {
            input = next_input;
            current_line = line;
            current_column = column;
            result.push(next_item);
        }

        Ok((input, current_line, current_column, result))
    }
}

fn pred<'a, P, A, F>(parser: P, predicate: F) -> impl Parser<'a, A>
where
    P: Parser<'a, A>,
    F: Fn(&A) -> bool,
    A: std::fmt::Display,
{
    move |input, line, column| {
        parser
            .parse(input, line, column)
            .and_then(|(next_input, ok_line, ok_column, value)| {
                if predicate(&value) {
                    Ok((next_input, ok_line, ok_column, value))
                } else {
                    Err(GrammarError {
                        err_info: format!("\"{value}\"不符合谓词条件"),
                        start: Position { line, column },
                        end: Position {
                            line: ok_line,
                            column: ok_column - 1,
                        },
                    })
                }
            })
    }
}

fn or<'a, P1, P2, R>(parser1: P1, parser2: P2) -> impl Parser<'a, R>
where
    P1: Parser<'a, R>,
    P2: Parser<'a, R>,
{
    move |input, line, column| match parser1.parse(input, line, column) {
        Ok(work) => Ok(work),
        Err(err1) => match parser2.parse(input, line, column) {
            Ok(work) => Ok(work),
            Err(err2) => Err(GrammarError {
                err_info: err1.err_info + &err2.err_info,
                start: err1.start,
                end: err1.end,
            }),
        },
    }
}

fn any_char(input: &str, line: usize, column: usize) -> ParseResult<char> {
    match input.chars().next() {
        Some(next) => {
            let current_line;
            let current_column;
            if next == '\n' {
                current_line = line + 1;
                current_column = 1;
            } else {
                current_line = line;
                current_column = column + next.len_utf8();
            }
            Ok((
                &input[next.len_utf8()..],
                current_line,
                current_column,
                next,
            ))
        }
        _ => Err(GrammarError {
            err_info: "空字符串".to_string(),
            start: Position { line, column },
            end: Position { line, column },
        }),
    }
}

fn whitespace_char<'a>() -> impl Parser<'a, char> {
    |input, line, column| match pred(any_char, |c| c.is_whitespace()).parse(input, line, column) {
        Ok(work) => Ok(work),
        Err(err) => Err(GrammarError {
            err_info: "缺少空格".to_string(),
            start: err.start,
            end: err.end,
        }),
    }
}

fn zero_more_whitespace<'a>() -> impl Parser<'a, Vec<char>> {
    zero_or_more(whitespace_char())
}

fn one_more_whitespace<'a>() -> impl Parser<'a, Vec<char>> {
    one_or_more(whitespace_char())
}

fn match_literal<'a>(expected: &'static str) -> impl Parser<'a, ()> {
    move |input: &'a str, line: usize, column: usize| match input.get(0..expected.len()) {
        Some(next) => {
            let current_line;
            let current_column;
            if next == expected {
                if next == "\n" {
                    current_line = line + 1;
                    current_column = 0;
                } else {
                    current_line = line;
                    current_column = column + expected.chars().count();
                }

                Ok((&input[expected.len()..], current_line, current_column, ()))
            } else {
                Err(GrammarError {
                    err_info: format!("缺失\"{expected}\""),
                    start: Position { line, column },
                    end: Position { line, column },
                })
            }
        }
        _ => Err(GrammarError {
            err_info: format!("缺失\"{expected}\""),
            start: Position { line, column },
            end: Position { line, column },
        }),
    }
}

pub fn parser(mut input: &str) -> Result<AST, Vec<GrammarError>> {
    let mut ast: AST = AST {
        children: Vec::new(),
    };
    let mut errs: Vec<GrammarError> = Vec::new();
    let mut current_line = 1;
    let mut current_column = 1;
    loop {
        match statement().parse(input, current_line, current_column) {
            Ok((next_input, line, column, stmt)) => {
                input = next_input;
                current_line = line;
                current_column = column;
                ast.children.push(stmt);
            }
            Err(err) => errs.push(err),
        }

        if input.is_empty() {
            break;
        }
    }

    if errs.is_empty() {
        Ok(ast)
    } else {
        Err(errs)
    }
}

/*
 * statement := (whitespace)* definition | application (whitespace)* ; (whitespace)*
 */
fn statement<'a>() -> impl Parser<'a, Stmt> {
    right(
        zero_more_whitespace(),
        left(
            |input, line, column| match definition().parse(input, line, column) {
                Ok((rest_input, line, column, def_expr)) => {
                    Ok((rest_input, line, column, Stmt::Definition(def_expr)))
                }
                _ => match application().parse(input, line, column) {
                    Ok((rest_input, line, column, app_expr)) => {
                        Ok((rest_input, line, column, Stmt::Application(app_expr)))
                    }
                    Err(err) => Err(GrammarError {
                        err_info: format!("\"{input}\"不是定义语句也不是应用语句"),
                        start: err.start,
                        end: err.end,
                    }),
                },
            },
            right(
                zero_more_whitespace(),
                left(match_literal(";"), zero_more_whitespace()),
            ),
        ),
    )
}

/*
 *  definition := def whitespace* variable (whitespace)* = (whitespace)* function
 */
fn definition<'a>() -> impl Parser<'a, DefinitionExpr> {
    right(
        match_literal("def"),
        right(one_more_whitespace(), |input, line, column| {
            variable(input, line, column).and_then(|(next_input_for_func, line, column, name)| {
                right(
                    zero_more_whitespace(),
                    right(
                        match_literal("="),
                        right(zero_more_whitespace(), function()),
                    ),
                )
                .parse(next_input_for_func, line, column)
                .map(|(rest_input, line, column, func_expr)| {
                    (rest_input, line, column, DefinitionExpr { name, func_expr })
                })
            })
        }),
    )
}

/*
 * application := '(' (whitespace)* func_expression whitespace* argu_expression (whitespace)* ')'
 */
fn application<'a>() -> impl Parser<'a, ApplicationExpr> {
    right(
        match_literal("("),
        right(
            zero_more_whitespace(),
            left(
                |input, line, column| {
                    expression().parse(input, line, column).and_then(
                        |(next_input, line, column, func_expr)| {
                            right(one_more_whitespace(), expression())
                                .parse(next_input, line, column)
                                .map(|(rest_input, line, column, argu_expr)| {
                                    (
                                        rest_input,
                                        line,
                                        column,
                                        ApplicationExpr {
                                            func_expr: Box::new(func_expr),
                                            argu_expr: Box::new(argu_expr),
                                        },
                                    )
                                })
                        },
                    )
                },
                right(zero_more_whitespace(), match_literal(")")),
            ),
        ),
    )
}

/*
 * function := λ variable . expression
 */
fn function<'a>() -> impl Parser<'a, FunctionExpr> {
    right(match_literal("λ"), |input, line, column| {
        variable(input, line, column).and_then(|(input_for_expr, line, column, parameter)| {
            right(match_literal("."), expression())
                .parse(input_for_expr, line, column)
                .map(|(rest_input, line, column, body)| {
                    (
                        rest_input,
                        line,
                        column,
                        FunctionExpr {
                            parameter,
                            body: Box::new(body),
                        },
                    )
                })
        })
    })
}

/*
 * expression := variable | function | application
 */
fn expression<'a>() -> impl Parser<'a, Expr> {
    move |input: &'a str, line, column| {
        if input.is_empty() {
            return Err(GrammarError {
                err_info: "表达式不可以空".to_string(),
                start: Position { line, column },
                end: Position { line, column },
            });
        }

        match variable(input, line, column) {
            Ok((rest_input, line, column, name)) => {
                Ok((rest_input, line, column, Expr::Literal(name)))
            }
            _ => match function().parse(input, line, column) {
                Ok((rest_input, line, column, func_expr)) => {
                    Ok((rest_input, line, column, Expr::Function(func_expr)))
                }
                _ => match application().parse(input, line, column) {
                    Ok((rest_input, line, column, app_expr)) => {
                        Ok((rest_input, line, column, Expr::Application(app_expr)))
                    }
                    Err(err) => Err(GrammarError {
                        err_info: format!("\"{input}\"不是变量,不是函数,也不是应用"),
                        start: err.start,
                        end: err.end,
                    }),
                },
            },
        }
    }
}

/*
 * 如果input匹配variable name成功,则返回(rest_input,matched)
 * 否则返回input
 */
fn variable(input: &str, line: usize, column: usize) -> ParseResult<String> {
    let mut matched = String::new();
    let mut chars = input.chars();
    let current_line = line;
    let mut current_column = column;
    match chars.next() {
        Some(next) => {
            if next.is_ascii_alphabetic() {
                matched.push(next);
                current_column += 1;
            } else {
                return Err(GrammarError {
                    err_info: format!("\"{next}\"不是ASCII中的字母"),
                    start: Position { line, column },
                    end: Position { line, column },
                });
            }
        }
        _ => {
            return Err(GrammarError {
                err_info: "变量不可以为空".to_string(),
                start: Position { line, column },
                end: Position { line, column },
            })
        }
    }

    for next in chars {
        if next.is_ascii_alphanumeric() || next == '_' {
            matched.push(next);
            current_column += 1;
        } else {
            break;
        }
    }

    let next_index = matched.len();
    Ok((&input[next_index..], current_line, current_column, matched))
}

#[cfg(test)]
mod tool_tests {
    use crate::parser::{
        variable, zero_more_whitespace, ApplicationExpr, DefinitionExpr, Expr, FunctionExpr,
        GrammarError, Parser, Position, Stmt,
    };

    use super::{
        any_char, application, definition, function, match_literal, one_more_whitespace, pair,
        pred, statement,
    };

    #[test]
    fn test_match_literal() {
        let parser = match_literal("Hello Lambda!");
        assert_eq!(Ok(("", 1, 14, ())), parser.parse("Hello Lambda!", 1, 1));

        assert_eq!(
            Ok((" Hello Functional Programming!", 1, 14, ())),
            parser.parse("Hello Lambda! Hello Functional Programming!", 1, 1)
        );

        assert_eq!(
            Err(GrammarError {
                err_info: "缺失\"Hello Lambda!\"".to_string(),
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            }),
            parser.parse("Hello Functional Programming!", 1, 1)
        )
    }

    #[test]
    fn test_pair_combinator() {
        let def = pair(match_literal("def"), variable);
        assert_eq!(
            Ok((" = λx.x", 1, 14, ((), "self_apply".to_string()))),
            def.parse("defself_apply = λx.x", 1, 1)
        );

        assert_eq!(
            Err(GrammarError {
                err_info: "缺失\"def\"".to_string(),
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            }),
            def.parse("self_apply = λx.x", 1, 1)
        );

        assert_eq!(
            Err(GrammarError {
                err_info: "缺失\"def\"".to_string(),
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            }),
            def.parse("= λx.x", 1, 1)
        )
    }

    #[test]
    fn test_any_char() {
        assert_eq!(any_char("omg", 1, 1), Ok(("mg", 1, 2, 'o')));
        assert_eq!(any_char(" lambda", 1, 1), Ok(("lambda", 1, 2, ' ')));
        assert_eq!(any_char(";(λx.x s)", 1, 1), Ok(("(λx.x s)", 1, 2, ';')));
        assert_eq!(
            any_char("", 1, 1),
            Err(GrammarError {
                err_info: "空字符串".to_string(),
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            })
        );
    }

    #[test]
    fn test_predicate_combinator() {
        let parser = pred(any_char, |c| *c == 'o');
        assert_eq!(Ok(("mg", 1, 2, 'o')), parser.parse("omg", 1, 1));
        assert_eq!(
            Err(GrammarError {
                err_info: "\"l\"不符合谓词条件".to_string(),
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            }),
            parser.parse("lol", 1, 1)
        );
        let parser = pred(any_char, |c| *c == ';');
        assert_eq!(Ok(("lambda", 1, 2, ';')), parser.parse(";lambda", 1, 1));
    }

    #[test]
    fn test_zero_more_whitespace() {
        let parser = zero_more_whitespace();
        assert_eq!(Ok(("", 1, 1, Vec::new())), parser.parse("", 1, 1));
        assert_eq!(Ok(("", 1, 2, vec![' '])), parser.parse(" ", 1, 1));
        assert_eq!(Ok(("", 2, 1, vec!['\n'])), parser.parse("\n", 1, 1));
        assert_eq!(
            Ok(("def", 2, 2, vec!['\n', ' '])),
            parser.parse("\n def", 1, 1)
        );
        assert_eq!(Ok(("", 1, 2, vec!['\t'])), parser.parse("\t", 1, 1));
        assert_eq!(
            Ok(("def", 1, 3, vec!['\t', ' '])),
            parser.parse("\t def", 1, 1)
        );
        assert_eq!(Ok(("", 1, 3, vec![' ', ' '])), parser.parse("  ", 1, 1));
        assert_eq!(
            Ok(("def", 1, 3, vec![' ', ' '])),
            parser.parse("  def", 1, 1)
        );
    }

    #[test]
    fn test_one_more_whitespace() {
        let parser = one_more_whitespace();
        assert_eq!(
            Err(GrammarError {
                err_info: "缺少空格".to_string(),
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            }),
            parser.parse("", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "缺少空格".to_string(),
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            }),
            parser.parse("self_apply", 1, 1)
        );
        assert_eq!(Ok(("", 1, 2, vec![' '])), parser.parse(" ", 1, 1));
        assert_eq!(Ok(("", 2, 1, vec!['\n'])), parser.parse("\n", 1, 1));
        assert_eq!(
            Ok(("def", 2, 2, vec!['\n', ' '])),
            parser.parse("\n def", 1, 1)
        );
        assert_eq!(Ok(("", 1, 2, vec!['\t'])), parser.parse("\t", 1, 1));
        assert_eq!(
            Ok(("def", 1, 3, vec!['\t', ' '])),
            parser.parse("\t def", 1, 1)
        );
        assert_eq!(Ok(("", 1, 3, vec![' ', ' '])), parser.parse("  ", 1, 1));
        assert_eq!(
            Ok(("def", 1, 3, vec![' ', ' '])),
            parser.parse("  def", 1, 1)
        );
    }

    #[test]
    fn test_variable() {
        assert_eq!(
            Ok(("", 1, 11, "self_apply".to_string())),
            variable("self_apply", 1, 1)
        );
        assert_eq!(
            Ok((" = λx.x", 1, 11, "self_apply".to_string())),
            variable("self_apply = λx.x", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "\"λ\"不是ASCII中的字母".to_string(),
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            }),
            variable("λx.x", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "变量不可以为空".to_string(),
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            }),
            variable("", 1, 1)
        )
    }

    #[test]
    fn test_function() {
        let parser = function();
        assert_eq!(
            Ok((
                ";",
                1,
                5,
                FunctionExpr {
                    parameter: "x".to_string(),
                    body: Box::new(Expr::Literal("x".to_string()))
                }
            )),
            parser.parse("λx.x;", 1, 1)
        );
        assert_eq!(
            Ok((
                ";",
                1,
                8,
                FunctionExpr {
                    parameter: "x".to_string(),
                    body: Box::new(Expr::Function(FunctionExpr {
                        parameter: "y".to_string(),
                        body: Box::new(Expr::Literal("x".to_string()))
                    }))
                }
            )),
            parser.parse("λx.λy.x;", 1, 1)
        );
        assert_eq!(
            Ok((
                ";",
                1,
                9,
                FunctionExpr {
                    parameter: "x".to_string(),
                    body: Box::new(Expr::Application(ApplicationExpr {
                        func_expr: Box::new(Expr::Literal("x".to_string())),
                        argu_expr: Box::new(Expr::Literal("x".to_string())),
                    }))
                }
            )),
            parser.parse("λx.(x x);", 1, 1)
        );

        assert_eq!(
            Err(GrammarError {
                err_info: "缺失\"λ\"".to_string(),
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            }),
            parser.parse("", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "缺失\"λ\"".to_string(),
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            }),
            parser.parse("x.x", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "变量不可以为空".to_string(),
                start: Position { line: 1, column: 2 },
                end: Position { line: 1, column: 2 }
            }),
            parser.parse("λ", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "\".\"不是ASCII中的字母".to_string(),
                start: Position { line: 1, column: 2 },
                end: Position { line: 1, column: 2 }
            }),
            parser.parse("λ.", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "缺失\".\"".to_string(),
                start: Position { line: 1, column: 3 },
                end: Position { line: 1, column: 3 }
            }),
            parser.parse("λx", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "缺失\".\"".to_string(),
                start: Position { line: 1, column: 3 },
                end: Position { line: 1, column: 3 }
            }),
            parser.parse("λx;", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "表达式不可以空".to_string(),
                start: Position { line: 1, column: 4 },
                end: Position { line: 1, column: 4 }
            }),
            parser.parse("λx.", 1, 1)
        );
    }

    #[test]
    fn test_definition() {
        let parser = definition();
        assert_eq!(
            Ok((
                ";",
                1,
                22,
                DefinitionExpr {
                    name: "self_apply".to_string(),
                    func_expr: FunctionExpr {
                        parameter: "x".to_string(),
                        body: Box::new(Expr::Literal("x".to_string()))
                    }
                }
            )),
            parser.parse("def self_apply = λx.x;", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "缺失\"def\"".to_string(),
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            }),
            parser.parse("self_apply = λx.x;", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "缺少空格".to_string(),
                start: Position { line: 1, column: 4 },
                end: Position { line: 1, column: 4 }
            }),
            parser.parse("def", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "缺少空格".to_string(),
                start: Position { line: 1, column: 4 },
                end: Position { line: 1, column: 4 }
            }),
            parser.parse("defself_apply", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "变量不可以为空".to_string(),
                start: Position { line: 1, column: 5 },
                end: Position { line: 1, column: 5 }
            }),
            parser.parse("def ", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "缺失\"=\"".to_string(),
                start: Position {
                    line: 1,
                    column: 15
                },
                end: Position {
                    line: 1,
                    column: 15
                }
            }),
            parser.parse("def self_apply", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "缺失\"λ\"".to_string(),
                start: Position {
                    line: 1,
                    column: 18
                },
                end: Position {
                    line: 1,
                    column: 18
                }
            }),
            parser.parse("def self_apply = ", 1, 1)
        );
    }

    #[test]
    fn test_application() {
        let parser = application();
        assert_eq!(
            Ok((
                ";",
                1,
                6,
                ApplicationExpr {
                    func_expr: Box::new(Expr::Literal("x".to_string())),
                    argu_expr: Box::new(Expr::Literal("x".to_string())),
                },
            )),
            parser.parse("(x x);", 1, 1)
        );

        assert_eq!(
            Ok((
                ";",
                1,
                9,
                ApplicationExpr {
                    func_expr: Box::new(Expr::Function(FunctionExpr {
                        parameter: "x".to_string(),
                        body: Box::new(Expr::Literal("x".to_string()))
                    })),
                    argu_expr: Box::new(Expr::Literal("s".to_string())),
                },
            )),
            parser.parse("(λx.x s);", 1, 1)
        );

        assert_eq!(
            Ok((
                ";",
                1,
                18,
                ApplicationExpr {
                    func_expr: Box::new(Expr::Literal("self_apply".to_string())),
                    argu_expr: Box::new(Expr::Function(FunctionExpr {
                        parameter: "s".to_string(),
                        body: Box::new(Expr::Literal("s".to_string()))
                    }))
                },
            )),
            parser.parse("(self_apply λs.s);", 1, 1)
        );

        assert_eq!(
            Ok((
                ";",
                1,
                12,
                ApplicationExpr {
                    func_expr: Box::new(Expr::Function(FunctionExpr {
                        parameter: "x".to_string(),
                        body: Box::new(Expr::Literal("x".to_string()))
                    })),
                    argu_expr: Box::new(Expr::Function(FunctionExpr {
                        parameter: "y".to_string(),
                        body: Box::new(Expr::Literal("y".to_string()))
                    }))
                },
            )),
            parser.parse("(λx.x λy.y);", 1, 1)
        );

        assert_eq!(
            Ok((
                ";",
                1,
                13,
                ApplicationExpr {
                    func_expr: Box::new(Expr::Function(FunctionExpr {
                        parameter: "x".to_string(),
                        body: Box::new(Expr::Literal("x".to_string()))
                    })),
                    argu_expr: Box::new(Expr::Application(ApplicationExpr {
                        func_expr: Box::new(Expr::Literal("s".to_string())),
                        argu_expr: Box::new(Expr::Literal("s".to_string()))
                    })),
                },
            )),
            parser.parse("(λx.x (s s));", 1, 1)
        );

        assert_eq!(
            Ok((
                ";",
                1,
                13,
                ApplicationExpr {
                    func_expr: Box::new(Expr::Application(ApplicationExpr {
                        func_expr: Box::new(Expr::Literal("x".to_string())),
                        argu_expr: Box::new(Expr::Literal("x".to_string()))
                    })),
                    argu_expr: Box::new(Expr::Function(FunctionExpr {
                        parameter: "s".to_string(),
                        body: Box::new(Expr::Literal("s".to_string()))
                    })),
                },
            )),
            parser.parse("((x x) λs.s);", 1, 1)
        );

        assert_eq!(
            Ok((
                ";",
                1,
                14,
                ApplicationExpr {
                    func_expr: Box::new(Expr::Application(ApplicationExpr {
                        func_expr: Box::new(Expr::Literal("x".to_string())),
                        argu_expr: Box::new(Expr::Literal("x".to_string()))
                    })),
                    argu_expr: Box::new(Expr::Application(ApplicationExpr {
                        func_expr: Box::new(Expr::Literal("s".to_string())),
                        argu_expr: Box::new(Expr::Literal("s".to_string()))
                    })),
                },
            )),
            parser.parse("((x x) (s s));", 1, 1)
        );

        assert_eq!(
            Err(GrammarError {
                err_info: "缺失\"(\"".to_string(),
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            }),
            parser.parse("x x);", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "表达式不可以空".to_string(),
                start: Position { line: 1, column: 2 },
                end: Position { line: 1, column: 2 }
            }),
            parser.parse("(", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "\".\"不是变量,不是函数,也不是应用".to_string(),
                start: Position { line: 1, column: 2 },
                end: Position { line: 1, column: 2 }
            }),
            parser.parse("(.", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "缺少空格".to_string(),
                start: Position { line: 1, column: 3 },
                end: Position { line: 1, column: 3 }
            }),
            parser.parse("(x", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "\".\"不是变量,不是函数,也不是应用".to_string(),
                start: Position { line: 1, column: 4 },
                end: Position { line: 1, column: 4 }
            }),
            parser.parse("(x .", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "缺失\")\"".to_string(),
                start: Position { line: 1, column: 5 },
                end: Position { line: 1, column: 5 }
            }),
            parser.parse("(x x", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "缺失\")\"".to_string(),
                start: Position { line: 1, column: 6 },
                end: Position { line: 1, column: 6 }
            }),
            parser.parse("(x x .", 1, 1)
        );
    }

    #[test]
    fn test_statement() {
        let parser = statement();
        assert_eq!(
            Ok((
                "(x x)",
                2,
                2,
                Stmt::Definition(DefinitionExpr {
                    name: "self_apply".to_string(),
                    func_expr: FunctionExpr {
                        parameter: "x".to_string(),
                        body: Box::new(Expr::Literal("x".to_string()))
                    }
                })
            )),
            parser.parse("def self_apply = λx.x;\n (x x)", 1, 1)
        );
        assert_eq!(
            Ok((
                "(x x)",
                2,
                2,
                Stmt::Application(ApplicationExpr {
                    func_expr: Box::new(Expr::Literal("x".to_string())),
                    argu_expr: Box::new(Expr::Literal("x".to_string()))
                })
            )),
            parser.parse("  (x x);  \n (x x)", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "缺失\";\"".to_string(),
                start: Position { line: 2, column: 1 },
                end: Position { line: 2, column: 1 }
            }),
            parser.parse("  (x x) \n", 1, 1)
        );
        assert_eq!(
            Err(GrammarError {
                err_info: "\"λx.x\"不是定义语句也不是应用语句".to_string(),
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            }),
            parser.parse("λx.x", 1, 1)
        );

    }
}
