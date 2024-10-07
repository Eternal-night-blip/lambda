use std::{fmt::Display, ops::Add, process::exit};

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Lambda,
    Literal(String),
    Number(String),
    LeftParenthesis,
    RightParenthesis,
    Def,
    Equal,
    Whitespace,
    Dot,
    Semicolon,
    EOF,
    Line,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TokenWithContext {
    pub token: Token,
    pub line: usize,
    pub column: usize,
}

impl Add for Token {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        if let (Token::Number(x), Token::Number(y)) = (self.clone(), other.clone()) {
            Token::Number(x + &y)
        } else if let (Token::Literal(x), Token::Literal(y)) = (self, other) {
            Token::Literal(x + &y)
        } else {
            println!("未定义的Token的Add操作");
            exit(0)
        }
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Literal(name) => write!(f, "Literal({name})"),
            Token::Number(num) => write!(f, "Number({num})"),
            _ => write!(f, "{:?}", self),
        }
    }
}

/*
 * 注意并不合并Whitespace
 */
pub fn scan(input: String) -> Vec<TokenWithContext> {
    if input.is_empty() {
        return vec![TokenWithContext {
            token: Token::EOF,
            line: 1,
            column: 1,
        }];
    }

    let mut current_line: usize = 1;
    let mut current_column: usize = 0;
    let raw_tokens: Vec<TokenWithContext> = input
        .chars()
        .map(|c| match c {
            'λ' => {
                current_column += 1;
                TokenWithContext {
                    token: Token::Lambda,
                    line: current_line,
                    column: current_column,
                }
            }
            'a'..='z' | 'A'..='Z' | '_' => {
                current_column += 1;
                TokenWithContext {
                    token: Token::Literal(c.to_string()),
                    line: current_line,
                    column: current_column,
                }
            }
            '0'..='9' => {
                current_column += 1;
                TokenWithContext {
                    token: Token::Number(c.to_string()),
                    line: current_line,
                    column: current_column,
                }
            }
            '(' => {
                current_column += 1;
                TokenWithContext {
                    token: Token::LeftParenthesis,
                    line: current_line,
                    column: current_column,
                }
            }
            ')' => {
                current_column += 1;
                TokenWithContext {
                    token: Token::RightParenthesis,
                    line: current_line,
                    column: current_column,
                }
            }

            '=' => {
                current_column += 1;
                TokenWithContext {
                    token: Token::Equal,
                    line: current_line,
                    column: current_column,
                }
            }
            '.' => {
                current_column += 1;
                TokenWithContext {
                    token: Token::Dot,
                    line: current_line,
                    column: current_column,
                }
            }
            ';' => {
                current_column += 1;
                TokenWithContext {
                    token: Token::Semicolon,
                    line: current_line,
                    column: current_column,
                }
            }
            ' ' => {
                current_column += 1;
                TokenWithContext {
                    token: Token::Whitespace,
                    line: current_line,
                    column: current_column,
                }
            }
            '\r' => {
                current_column += 1;
                TokenWithContext {
                    token: Token::Whitespace,
                    line: current_line,
                    column: current_column,
                }
            }
            '\t' => {
                current_column += 1;
                TokenWithContext {
                    token: Token::Whitespace,
                    line: current_line,
                    column: current_column,
                }
            }
            '\n' => {
                current_column += 1;
                let token = TokenWithContext {
                    token: Token::Line,
                    line: current_line,
                    column: current_column,
                };
                current_line += 1;
                current_column = 0;
                token
            }
            other => {
                println!(
                    "在第{current_line}行,第{current_column}列,发现非法符号\"{other}\"."
                );
                exit(0);
            }
        })
        .collect();

    let mut current_index: usize = 0;
    let last_index = raw_tokens.len() - 1;
    let mut tokens: Vec<TokenWithContext> = Vec::new();

    while current_index <= last_index {
        if let Token::Number(_) = raw_tokens[current_index].token {
            //获取完整的数字,将相邻的Number合并
            //识别最后一个Number所在的索引
            let mut end_index = current_index;
            while end_index < last_index {
                match raw_tokens[end_index + 1].token {
                    Token::Number(_) => end_index += 1,
                    _ => break,
                }
            }

            tokens.push(raw_tokens[current_index..=end_index].iter().fold(
                TokenWithContext {
                    token: Token::Number("".to_string()),
                    line: raw_tokens[current_index].line,
                    column: raw_tokens[current_index].column,
                },
                |acc, x| TokenWithContext {
                    token: acc.token + x.token.clone(),
                    line: acc.line,
                    column: acc.column,
                },
            ));

            current_index = end_index + 1;
        } else if let Token::Literal(_) = raw_tokens[current_index].token {
            let mut end = current_index;

            while end < last_index {
                match raw_tokens[end + 1].token {
                    Token::Literal(_) => end += 1,
                    _ => break,
                }
            }
            let object = raw_tokens[current_index..=end].iter().fold(
                TokenWithContext {
                    token: Token::Literal("".to_string()),
                    line: raw_tokens[current_index].line,
                    column: raw_tokens[current_index].column,
                },
                |acc, x| TokenWithContext {
                    token: acc.token + x.token.clone(),
                    line: acc.line,
                    column: acc.column,
                },
            );

            if let Token::Literal(ref def) = object.token {
                if *def == "def".to_string() {
                    tokens.push(TokenWithContext {
                        token: Token::Def,
                        line: object.line,
                        column: object.column,
                    });
                } else {
                    tokens.push(object);
                }
            }
            current_index = end + 1;
        } else {
            if raw_tokens[current_index].token != Token::Line {
                tokens.push(raw_tokens[current_index].clone());
            }
            current_index += 1;
        }
    }

    tokens.push(TokenWithContext {
        token: Token::EOF,
        line: current_line,
        column: current_column + 1,
    });

    tokens
}

#[cfg(test)]
mod scanner_tests {
    use crate::scanner::Token::*;
    use crate::scanner::TokenWithContext;

    use super::scan;
    #[test]
    fn check_token_add() {
        assert_eq!(
            Literal("x".to_string()),
            Literal("".to_string()) + Literal("x".to_string())
        );
        assert_eq!(
            Literal("xy".to_string()),
            Literal("x".to_string()) + Literal("y".to_string())
        );
        assert_eq!(
            Literal("x_y".to_string()),
            Literal("x".to_string()) + Literal("_".to_string()) + Literal("y".to_string())
        );
        assert_eq!(
            Number("1".to_string()),
            Number("".to_string()) + Number("1".to_string())
        );
        assert_eq!(
            Number("01".to_string()),
            Number("0".to_string()) + Number("1".to_string())
        );
    }

    #[test]
    fn check_display() {
        assert_eq!("Lambda", format!("{}", Lambda));
        assert_eq!("Literal(peek)", format!("{}", Literal("peek".to_string())));
        assert_eq!("Number(231)", format!("{}", Number("231".to_string())));
        assert_eq!("LeftParenthesis", format!("{}", LeftParenthesis));
        assert_eq!("RightParenthesis", format!("{}", RightParenthesis));
        assert_eq!("Def", format!("{}", Def));
        assert_eq!("Equal", format!("{}", Equal));
        assert_eq!("Whitespace", format!("{}", Whitespace));
        assert_eq!("Dot", format!("{}", Dot));
        assert_eq!("Semicolon", format!("{}", Semicolon));
        assert_eq!("Line", format!("{}", Line));
        assert_eq!("EOF", format!("{}", EOF));
    }

    #[test]
    fn check_scan() {
        assert_eq!(
            scan("".to_string()),
            vec![TokenWithContext {
                token: EOF,
                line: 1,
                column: 1
            }]
        );
        assert_eq!(
            scan("λ".to_string()),
            vec![
                TokenWithContext {
                    token: Lambda,
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: EOF,
                    line: 1,
                    column: 2
                },
            ]
        );
        assert_eq!(
            scan("(".to_string()),
            vec![
                TokenWithContext {
                    token: LeftParenthesis,
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: EOF,
                    line: 1,
                    column: 2
                },
            ]
        );
        assert_eq!(
            scan(")".to_string()),
            vec![
                TokenWithContext {
                    token: RightParenthesis,
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: EOF,
                    line: 1,
                    column: 2
                },
            ]
        );
        assert_eq!(
            scan(".".to_string()),
            vec![
                TokenWithContext {
                    token: Dot,
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: EOF,
                    line: 1,
                    column: 2
                },
            ]
        );
        assert_eq!(
            scan("=".to_string()),
            vec![
                TokenWithContext {
                    token: Equal,
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: EOF,
                    line: 1,
                    column: 2
                },
            ]
        );
        assert_eq!(
            scan(";".to_string()),
            vec![
                TokenWithContext {
                    token: Semicolon,
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: EOF,
                    line: 1,
                    column: 2
                },
            ]
        );
        assert_eq!(
            scan(" ".to_string()),
            vec![
                TokenWithContext {
                    token: Whitespace,
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: EOF,
                    line: 1,
                    column: 2
                },
            ]
        );
        assert_eq!(
            scan("\r".to_string()),
            vec![
                TokenWithContext {
                    token: Whitespace,
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: EOF,
                    line: 1,
                    column: 2
                },
            ]
        );
        assert_eq!(
            scan("\t".to_string()),
            vec![
                TokenWithContext {
                    token: Whitespace,
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: EOF,
                    line: 1,
                    column: 2
                },
            ]
        );
        assert_eq!(
            scan("\n".to_string()),
            vec![
                TokenWithContext {
                    token: EOF,
                    line: 2,
                    column: 1
                },
            ]
        );
        assert_eq!(
            scan("x".to_string()),
            vec![
                TokenWithContext {
                    token: Literal("x".to_string()),
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: EOF,
                    line: 1,
                    column: 2
                },
            ]
        );
        assert_eq!(
            scan("W".to_string()),
            vec![
                TokenWithContext {
                    token: Literal("W".to_string()),
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: EOF,
                    line: 1,
                    column: 2
                },
            ]
        );
        assert_eq!(
            scan("_".to_string()),
            vec![
                TokenWithContext {
                    token: Literal("_".to_string()),
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: EOF,
                    line: 1,
                    column: 2
                },
            ]
        );
        assert_eq!(
            scan("3".to_string()),
            vec![
                TokenWithContext {
                    token: Number("3".to_string()),
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: EOF,
                    line: 1,
                    column: 2
                },
            ]
        );
        assert_eq!(
            scan("def".to_string()),
            vec![
                TokenWithContext {
                    token: Def,
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: EOF,
                    line: 1,
                    column: 4
                },
            ]
        );

        let input = "λxy.xy".to_string();

        assert_eq!(
            scan(input),
            vec![
                TokenWithContext {
                    token: Lambda,
                    line: 1,
                    column: 1
                },
                TokenWithContext {
                    token: Literal("xy".to_string()),
                    line: 1,
                    column: 2
                },
                TokenWithContext {
                    token: Dot,
                    line: 1,
                    column: 4
                },
                TokenWithContext {
                    token: Literal("xy".to_string()),
                    line: 1,
                    column: 5
                },
                TokenWithContext {
                    token: EOF,
                    line: 1,
                    column: 7
                },
            ]
        );
    }
}
