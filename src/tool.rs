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

type ParseResult<'a, Output> = Result<(&'a str, Output), String>;

trait Parser<'a, Output> {
    fn parse(&self, input: &'a str) -> ParseResult<'a, Output>;
}

impl<'a, F, Output> Parser<'a, Output> for F
where
    F: Fn(&'a str) -> ParseResult<Output>,
{
    fn parse(&self, input: &'a str) -> ParseResult<'a, Output> {
        self(input)
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
    move |input| {
        parser
            .parse(input)
            .map(|(next_input, result)| (next_input, converter(result)))
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
    move |input| {
        parser1.parse(input).and_then(|(next_input, result1)| {
            parser2
                .parse(next_input)
                .map(|(final_input, result2)| (final_input, (result1, result2)))
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
    move |mut input| {
        let mut result = Vec::new();

        while let Ok((next_input, next_item)) = parser.parse(input) {
            input = next_input;
            result.push(next_item);
        }

        Ok((input, result))
    }
}

fn one_or_more<'a, P, A>(parser: P) -> impl Parser<'a, Vec<A>>
where
    P: Parser<'a, A>,
{
    move |mut input| {
        let mut result = Vec::new();

        if let Ok((next_input, first_item)) = parser.parse(input) {
            input = next_input;
            result.push(first_item);
        } else {
            return Err(format!("解析{input}失败"));
        }

        while let Ok((next_input, next_item)) = parser.parse(input) {
            input = next_input;
            result.push(next_item);
        }

        Ok((input, result))
    }
}

fn pred<'a, P, A, F>(parser: P, predicate: F) -> impl Parser<'a, A>
where
    P: Parser<'a, A>,
    F: Fn(&A) -> bool,
{
    move |input| {
        parser.parse(input).and_then(|(next_input, value)| {
            if predicate(&value) {
                Ok((next_input, value))
            } else {
                Err(format!("\"{input}\"不符合谓词条件"))
            }
        })
    }
}

fn or<'a, P1, P2, R>(parser1: P1, parser2: P2) -> impl Parser<'a, R>
where
    P1: Parser<'a, R>,
    P2: Parser<'a, R>,
{
    move |input| match parser1.parse(input) {
        Ok(work) => Ok(work),
        Err(err1) => match parser2.parse(input) {
            Ok(work) => Ok(work),
            Err(err2) => Err(format!("or运算失败,皆不可解析:{err1},{err2}")),
        },
    }
}

fn any_char(input: &str) -> ParseResult<char> {
    match input.chars().next() {
        Some(next) => Ok((&input[next.len_utf8()..], next)),
        _ => Err("空字符串".to_string()),
    }
}

fn whitespace_char<'a>() -> impl Parser<'a, char> {
    pred(any_char, |c| c.is_whitespace())
}

fn zero_more_whitespace<'a>() -> impl Parser<'a, Vec<char>> {
    zero_or_more(whitespace_char())
}

fn one_more_whitespace<'a>() -> impl Parser<'a, Vec<char>> {
    one_or_more(whitespace_char())
}

fn match_literal<'a>(expected: &'static str) -> impl Parser<'a, ()> {
    move |input: &'a str| match input.get(0..expected.len()) {
        Some(next) => {
            if next == expected {
                Ok((&input[expected.len()..], ()))
            } else {
                Err(format!("应该是\"{expected}\",而不是\"{next}\""))
            }
        }
        _ => Err(format!("缺失\"{expected}\"")),
    }
}

pub fn parser(mut input: &str) -> Result<AST, Vec<String>> {
    let mut ast: AST = AST {
        children: Vec::new(),
    };
    let mut errs: Vec<String> = Vec::new();
    loop {
        match statement().parse(input) {
            Ok((next_input, stmt)) => {
                input = next_input;
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
            |input| match definition().parse(input) {
                Ok((rest_input, def_expr)) => Ok((rest_input, Stmt::Definition(def_expr))),
                _ => match application().parse(input) {
                    Ok((rest_input, app_expr)) => Ok((rest_input, Stmt::Application(app_expr))),
                    _ => Err(format!("\"{input}\"不是定义语句也不是应用语句")),
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
        right(one_more_whitespace(), |input| {
            variable(input).and_then(|(next_input_for_func, name)| {
                right(
                    zero_more_whitespace(),
                    right(
                        match_literal("="),
                        right(zero_more_whitespace(), function()),
                    ),
                )
                .parse(next_input_for_func)
                .map(|(rest_input, func_expr)| (rest_input, DefinitionExpr { name, func_expr }))
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
                |input| {
                    expression()
                        .parse(input)
                        .and_then(|(next_input, func_expr)| {
                            right(one_more_whitespace(), expression())
                                .parse(next_input)
                                .map(|(rest_input, argu_expr)| {
                                    (
                                        rest_input,
                                        ApplicationExpr {
                                            func_expr: Box::new(func_expr),
                                            argu_expr: Box::new(argu_expr),
                                        },
                                    )
                                })
                        })
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
    right(match_literal("λ"), |input| {
        variable(input).and_then(|(input_for_expr, parameter)| {
            right(match_literal("."), expression())
                .parse(input_for_expr)
                .map(|(rest_input, body)| {
                    (
                        rest_input,
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
    move |input| match variable(input) {
        Ok((rest_input, name)) => Ok((rest_input, Expr::Literal(name))),
        _ => match function().parse(input) {
            Ok((rest_input, func_expr)) => Ok((rest_input, Expr::Function(func_expr))),
            _ => match application().parse(input) {
                Ok((rest_input, app_expr)) => Ok((rest_input, Expr::Application(app_expr))),
                _ => Err(format!("\"{input}\"不是变量,不是函数,也不是应用")),
            },
        },
    }
}

/*
 * 如果input匹配variable name成功,则返回(rest_input,matched)
 * 否则返回input
 */
fn variable(input: &str) -> ParseResult<String> {
    let mut matched = String::new();
    let mut chars = input.chars();

    match chars.next() {
        Some(next) => {
            if next.is_ascii_alphabetic() {
                matched.push(next);
            } else {
                return Err(format!("\"{next}\"不是ASCII中的字母"));
            }
        }
        _ => return Err("变量不可以为空".to_string()),
    }

    for next in chars {
        if next.is_ascii_alphanumeric() || next == '_' {
            matched.push(next);
        } else {
            break;
        }
    }

    let next_index = matched.len();
    Ok((&input[next_index..], matched))
}

#[cfg(test)]
mod tool_tests {
    use crate::tool::{
        variable, zero_more_whitespace, ApplicationExpr, DefinitionExpr, Expr, FunctionExpr,
        Parser, Stmt,
    };

    use super::{
        any_char, application, definition, function, match_literal, one_more_whitespace, pair,
        pred, statement,
    };

    #[test]
    fn test_match_literal() {
        let parser = match_literal("Hello Lambda!");
        assert_eq!(Ok(("", ())), parser.parse("Hello Lambda!"));

        assert_eq!(
            Ok((" Hello Functional Programming!", ())),
            parser.parse("Hello Lambda! Hello Functional Programming!")
        );

        assert_eq!(
            Err("应该是\"Hello Lambda!\",而不是\"Hello Functio\"".to_string()),
            parser.parse("Hello Functional Programming!")
        )
    }

    #[test]
    fn test_pair_combinator() {
        let def = pair(match_literal("def"), variable);
        assert_eq!(
            Ok((" = λx.x", ((), "self_apply".to_string()))),
            def.parse("defself_apply = λx.x")
        );

        assert_eq!(
            Err("应该是\"def\",而不是\"sel\"".to_string()),
            def.parse("self_apply = λx.x")
        );

        assert_eq!(
            Err("应该是\"def\",而不是\"= d\"".to_string()),
            def.parse("= defλx.x")
        )
    }

    #[test]
    fn test_any_char() {
        assert_eq!(any_char("omg"), Ok(("mg", 'o')));
        assert_eq!(any_char(" lambda"), Ok(("lambda", ' ')));
        assert_eq!(any_char(";(λx.x s)"), Ok(("(λx.x s)", ';')));
        assert_eq!(any_char(""), Err("空字符串".to_string()));
    }

    #[test]
    fn test_predicate_combinator() {
        let parser = pred(any_char, |c| *c == 'o');
        assert_eq!(Ok(("mg", 'o')), parser.parse("omg"));
        assert_eq!(
            Err("\"lol\"不符合谓词条件".to_string()),
            parser.parse("lol")
        );
        let parser = pred(any_char, |c| *c == ';');
        assert_eq!(Ok(("lambda", ';')), parser.parse(";lambda"));
    }

    #[test]
    fn test_zero_more_whitespace() {
        let parser = zero_more_whitespace();
        assert_eq!(Ok(("", Vec::new())), parser.parse(""));
        assert_eq!(Ok(("", vec![' '])), parser.parse(" "));
        assert_eq!(Ok(("", vec!['\n'])), parser.parse("\n"));
        assert_eq!(Ok(("", vec!['\t'])), parser.parse("\t"));
        assert_eq!(Ok(("", vec![' ', ' '])), parser.parse("  "));
        assert_eq!(Ok(("def", vec![' ', ' '])), parser.parse("  def"));
    }

    #[test]
    fn test_one_more_whitespace() {
        let parser = one_more_whitespace();
        assert_eq!(Err("解析失败".to_string()), parser.parse(""));
        assert_eq!(Ok(("", vec![' '])), parser.parse(" "));
        assert_eq!(Ok(("", vec!['\n'])), parser.parse("\n"));
        assert_eq!(Ok(("", vec!['\t'])), parser.parse("\t"));
        assert_eq!(Ok(("", vec![' ', ' '])), parser.parse("  "));
        assert_eq!(Ok(("def", vec![' ', ' '])), parser.parse("  def"));
    }

    #[test]
    fn test_variable() {
        assert_eq!(Ok(("", "self_apply".to_string())), variable("self_apply"));
        assert_eq!(
            Ok((" = λx.x", "self_apply".to_string())),
            variable("self_apply = λx.x")
        );
        assert_eq!(Err("\"λ\"不是ASCII中的字母".to_string()), variable("λx.x"))
    }

    #[test]
    fn test_function() {
        let parser = function();
        assert_eq!(
            Ok((
                ";",
                FunctionExpr {
                    parameter: "x".to_string(),
                    body: Box::new(Expr::Literal("x".to_string()))
                }
            )),
            parser.parse("λx.x;")
        );
        assert_eq!(
            Ok((
                ";",
                FunctionExpr {
                    parameter: "x".to_string(),
                    body: Box::new(Expr::Function(FunctionExpr {
                        parameter: "y".to_string(),
                        body: Box::new(Expr::Literal("x".to_string()))
                    }))
                }
            )),
            parser.parse("λx.λy.x;")
        );
        assert_eq!(
            Ok((
                ";",
                FunctionExpr {
                    parameter: "x".to_string(),
                    body: Box::new(Expr::Application(ApplicationExpr {
                        func_expr: Box::new(Expr::Literal("x".to_string())),
                        argu_expr: Box::new(Expr::Literal("x".to_string())),
                    }))
                }
            )),
            parser.parse("λx.(x x);")
        );

        assert_eq!(Err("缺失\"λ\"".to_string()), parser.parse(""));
        assert_eq!(Err("变量不可以为空".to_string()), parser.parse("λ"));
        assert_eq!(
            Err("\".\"不是ASCII中的字母".to_string()),
            parser.parse("λ.")
        );
        assert_eq!(Err("缺失\".\"".to_string()), parser.parse("λx"));
        assert_eq!(
            Err("应该是\".\",而不是\";\"".to_string()),
            parser.parse("λx;")
        );
        assert_eq!(
            Err("\"\"不是变量,不是函数,也不是应用".to_string()),
            parser.parse("λx.")
        );
    }

    #[test]
    fn test_definition() {
        let parser = definition();
        assert_eq!(
            Ok((
                ";",
                DefinitionExpr {
                    name: "self_apply".to_string(),
                    func_expr: FunctionExpr {
                        parameter: "x".to_string(),
                        body: Box::new(Expr::Literal("x".to_string()))
                    }
                }
            )),
            parser.parse("def self_apply = λx.x;")
        );
        assert_eq!(
            Err("应该是\"def\",而不是\"sel\"".to_string()),
            parser.parse("self_apply = λx.x;")
        );
        assert_eq!(Err("解析失败".to_string()), parser.parse("def"));
        assert_eq!(Err("变量不可以为空".to_string()), parser.parse("def "));
        assert_eq!(Err("缺失\"=\"".to_string()), parser.parse("def self_apply"));
        assert_eq!(
            Err("缺失\"λ\"".to_string()),
            parser.parse("def self_apply = ")
        );
    }

    #[test]
    fn test_application() {
        let parser = application();
        assert_eq!(
            Ok((
                ";",
                ApplicationExpr {
                    func_expr: Box::new(Expr::Literal("x".to_string())),
                    argu_expr: Box::new(Expr::Literal("x".to_string())),
                },
            )),
            parser.parse("(x x);")
        );

        assert_eq!(
            Ok((
                ";",
                ApplicationExpr {
                    func_expr: Box::new(Expr::Function(FunctionExpr {
                        parameter: "x".to_string(),
                        body: Box::new(Expr::Literal("x".to_string()))
                    })),
                    argu_expr: Box::new(Expr::Literal("s".to_string())),
                },
            )),
            parser.parse("(λx.x s);")
        );

        assert_eq!(
            Ok((
                ";",
                ApplicationExpr {
                    func_expr: Box::new(Expr::Literal("self_apply".to_string())),
                    argu_expr: Box::new(Expr::Function(FunctionExpr {
                        parameter: "s".to_string(),
                        body: Box::new(Expr::Literal("s".to_string()))
                    }))
                },
            )),
            parser.parse("(self_apply λs.s);")
        );

        assert_eq!(
            Ok((
                ";",
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
            parser.parse("(λx.x λy.y);")
        );

        assert_eq!(
            Ok((
                ";",
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
            parser.parse("(λx.x (s s));")
        );

        assert_eq!(
            Ok((
                ";",
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
            parser.parse("((x x) λs.s);")
        );

        assert_eq!(
            Ok((
                ";",
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
            parser.parse("((x x) (s s));")
        );

        assert_eq!(
            Err("应该是\"(\",而不是\"x\"".to_string()),
            parser.parse("x x);")
        );
        assert_eq!(
            Err("\"\"不是变量,不是函数,也不是应用".to_string()),
            parser.parse("(")
        );
        assert_eq!(
            Err("\".\"不是变量,不是函数,也不是应用".to_string()),
            parser.parse("(.")
        );
        assert_eq!(Err("解析失败".to_string()), parser.parse("(x"));
        assert_eq!(
            Err("\".\"不是变量,不是函数,也不是应用".to_string()),
            parser.parse("(x .")
        );
        assert_eq!(Err("缺失\")\"".to_string()), parser.parse("(x x"));
        assert_eq!(
            Err("应该是\")\",而不是\".\"".to_string()),
            parser.parse("(x x .")
        );
    }

    #[test]
    fn test_statement() {
        let parser = statement();
        assert_eq!(
            Ok((
                "",
                Stmt::Application(ApplicationExpr {
                    func_expr: Box::new(Expr::Literal("x".to_string())),
                    argu_expr: Box::new(Expr::Literal("x".to_string()))
                })
            )),
            parser.parse("  (x x);  \n")
        );
        assert_eq!(Err("缺失\";\"".to_string()), parser.parse("  (x x) \n"));
    }
}
