use std::{collections::HashMap, process::exit};

use crate::parser::{
    ApplicationExpr, DefinitionExpr,
    Expr::{self, *},
    FunctionExpr, Stmt, AST,
};

struct Symbol {
    name: String,
    value: SymbolValue,
}

#[derive(Clone)]
enum SymbolValue {
    Name(String),
    Function(FunctionExpr),
    Application(ApplicationExpr),
}

type SymbolTable = HashMap<String, Symbol>;

type FunctionScope = String;

//我们采用延迟计算,而非及时计算

pub fn interpret(ast: AST) {
    let mut symbol_table: SymbolTable = HashMap::new();
    for stmt in ast.children {
        evaluate_stmt(stmt, &mut symbol_table);
    }
}

fn evaluate_stmt(stmt: Stmt, symbol_table: &mut SymbolTable) {
    match stmt {
        Stmt::Definition(definition_expr) => evaluate_def(definition_expr, symbol_table),
        Stmt::Application(application_expr) => {
            println!("{}", expr_to_string_app(application_expr.clone()));
            let result = evaluate_app(application_expr, symbol_table);
            println!("=> {}", expr_to_string(result));
        }
    }
}

/*
 * 将 def <name> = <function> 中的<name>添加到符号表,此<name>是Function类型
 */
fn evaluate_def(def_expr: DefinitionExpr, symbol_table: &mut SymbolTable) {
    let name = def_expr.name.clone();
    let symbol = Symbol {
        name: def_expr.name,
        value: SymbolValue::Function(def_expr.func_expr),
    };
    symbol_table.insert(name, symbol); //允许重新定义<name>是什么,可能的情况是符号表中已经有了<name>
}

/*
 * 计算的入口
 * 将<argument expression> 带入 <function expression>
 */
fn evaluate_app(app_expr: ApplicationExpr, symbol_table: &mut SymbolTable) -> Expr {
    let app_expr_for_compute = app_expr.clone();
    let func_expr = app_expr_for_compute.func_expr;
    let argu_expr = app_expr_for_compute.argu_expr;
    //需要判断是否是无限循环(不停机了)
    //比如(λx.(x x) λx.(x x))
    //注意如果是(λs.(s s) λx.(x x))仍会继续计算，直到(λx.(x x) λx.(x x))将终止,这是方便检查无限循环模式
    check_terminate(*func_expr.clone(), *argu_expr.clone());
    match *func_expr {
        Literal(name) => {
            //检查name是否是被定义的,如果是被定义的,则应该进行函数展开
            // (identity x)
            // (s y)
            match symbol_table.get(&name) {
                Some(symbol) => match &symbol.value {
                    SymbolValue::Name(unknown) => {
                        println!("语义错误:变量{name}不可以是被定义为字面量{unknown}");
                        exit(0)
                    }
                    SymbolValue::Application(_) => {
                        println!("语义错误,变量{name}不可以是被定义为应用语句");
                        exit(0);
                    }

                    SymbolValue::Function(function_expr) => {
                        let new_app_expr =
                            replace_func_expr_app(function_expr.clone(), app_expr.clone());
                        println!(
                            "replace \"{name}\" with \"{}\" ",
                            expr_to_string_func(function_expr.clone())
                        );
                        println!(
                            "then \"{}\" to \"{}\"",
                            expr_to_string_app(app_expr),
                            expr_to_string_app(new_app_expr.clone())
                        );
                        evaluate_app(new_app_expr, symbol_table)
                    }
                },
                None => {
                    return Expr::Application(ApplicationExpr {
                        func_expr: app_expr.func_expr,
                        argu_expr,
                    });
                }
            }
        }

        Function(function_expr) => evaluate_func(function_expr, *argu_expr, symbol_table),
        //先计算内层应用表达式,再把外层的参数表达式带入内层
        Application(application_expr) => {
            let result: Expr = evaluate_app(application_expr.clone(), symbol_table);
            //我们已经计算到底了,现在将
            println!(
                "=> {}",
                expr_to_string_app(ApplicationExpr {
                    func_expr: Box::new(result.clone()),
                    argu_expr: argu_expr.clone()
                })
            );
            match result {
                Application(ref result_app_expr) => {
                    //是不是注定返回和application_expr相同的
                    println!("=> {}", expr_to_string(result.clone()));
                    assert_eq!(application_expr, result_app_expr.clone());
                    println!("计算错误:无限计算");
                    exit(0);
                }
                Literal(name) => match symbol_table.get(&name) {
                    Some(symbol) => match &symbol.value {
                        SymbolValue::Application(_) => {
                            println!("语义错误:变量{name}不可以是被定义为应用语句");
                            exit(0);
                        }
                        SymbolValue::Name(_) => {
                            //todo 下列代码合理吗？
                            let result = Expr::Application(ApplicationExpr {
                                func_expr: Box::new(Expr::Literal(name)),
                                argu_expr,
                            });
                            return result;
                        }
                        SymbolValue::Function(function_expr) => {
                            evaluate_func(function_expr.clone(), *argu_expr, symbol_table)
                        }
                    },
                    None => {
                        panic!("计算错误:{name}未找到")
                    }
                },
                Function(function_expr) => evaluate_func(function_expr, *argu_expr, symbol_table),
            }
        }
    }
}

//检查模式(λx.(x x) λx.(x x))
fn check_terminate(func_expr: Expr, argu_expr: Expr) {
    match (func_expr.clone(), argu_expr.clone()) {
        (Function(function_expr), Function(argument_expr)) => {
            if function_expr == argument_expr {
                let para = function_expr.parameter;
                match *function_expr.body {
                    Application(application_expr) => {
                        match (*application_expr.func_expr, *application_expr.argu_expr) {
                            (Literal(name1), Literal(name2)) => {
                                if para == name1 && para == name2 {
                                    let origin = ApplicationExpr {
                                        func_expr: Box::new(func_expr),
                                        argu_expr: Box::new(argu_expr),
                                    };
                                    println!("{}将进行无限计算\n", expr_to_string_app(origin));
                                    exit(0)
                                }
                            }
                            _ => {}
                        }
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }
}

// evaluate_func就是beta reduction
fn evaluate_func(
    func_expr: FunctionExpr,
    actual_para: Expr,
    symbol_table: &mut SymbolTable,
) -> Expr {
    let formal_para = func_expr.parameter;
    let body = func_expr.body;
    let result = match *body {
        Literal(name) => beta_reduction_in_literal(formal_para, actual_para, name),

        Function(func_expr_in_body) => {
            beta_reduction_in_func(formal_para, actual_para, func_expr_in_body)
        }

        Application(app_expr_in_body) => {
            let mut scope = formal_para.clone();
            beta_reduction_in_app(formal_para, actual_para, app_expr_in_body, &mut scope)
        }
    };

    match result {
        Literal(_) => return result, //还是说要判定是否在符号表?不判定是否是延迟计算
        Function(_) => return result,
        Application(application_expr) => {
            println!("=> {}", expr_to_string_app(application_expr.clone()));
            return evaluate_app(application_expr, symbol_table);
        }
    }
}

fn beta_reduction_in_literal(from: String, to: Expr, name: String) -> Expr {
    if from == name {
        //对应λx.x,直接返回实参to
        return to;
    } else {
        //对应λx.y,与实参无关,返回y
        return Expr::Literal(name);
    }
}

//注意内层形参屏蔽外层同名形参
//from是外层形参,para是内层形参
fn beta_reduction_in_func(from: String, to: Expr, expr: FunctionExpr) -> Expr {
    let para = expr.parameter.clone();
    let body = expr.body.clone();
    match *body {
        Literal(inner_literal) => {
            if inner_literal == from && inner_literal != para {
                let body = Box::new(to);
                return Expr::Function(FunctionExpr {
                    parameter: para,
                    body,
                });
            } else {
                return Expr::Function(expr);
            }
        }
        Function(inner_expr) => {
            let body = Box::new(beta_reduction_in_func(from, to, inner_expr));
            return Expr::Function(FunctionExpr {
                parameter: para,
                body,
            });
        }

        Application(inner_expr) => {
            let mut inner_scope = para.clone();
            let body = Box::new(beta_reduction_in_app(
                from.clone(),
                to.clone(),
                inner_expr.clone(),
                &mut inner_scope,
            ));
            //判断是否需要进行alpha转换,不等则需要进行alpha转换
            if para == inner_scope {
                return Expr::Function(FunctionExpr {
                    parameter: para,
                    body,
                });
            } else {
                let mut inner_expr_replaced = inner_expr;
                inner_expr_replaced =
                    rename_formal_para_app(para, inner_scope.clone(), inner_expr_replaced);
                let body = Box::new(beta_reduction_in_app(
                    from,
                    to,
                    inner_expr_replaced,
                    &mut inner_scope,
                ));
                return Expr::Function(FunctionExpr {
                    parameter: inner_scope,
                    body,
                });
            }
        }
    }
}

//这里可能会出现名称冲突,要实现alpha转换
fn beta_reduction_in_app(
    from: String,
    to: Expr,
    expr: ApplicationExpr,
    scope: &mut FunctionScope,
) -> Expr {
    let func_expr = expr.func_expr.clone();
    let argu_expr = expr.argu_expr.clone();
    match (*func_expr, *argu_expr) {
        (Literal(name1), Literal(name2)) => {
            //可能会出现名称冲突
            if let Literal(to_name) = to.clone() {
                if to_name == *scope
                    && from != *scope
                    && ((name1 == from && name2 == *scope) || (name1 == *scope && name2 == from))
                {
                    //当from替换成to时与scope发生名称冲突,实现alpha转换,此时将scope进行重命名,然后回溯,这里就是把to原封不动地返回
                    *scope = format!("{scope}_for_alpha_conversion");
                    return to;
                } else {
                    let func_expr;
                    let argu_expr;
                    if name1 == from {
                        func_expr = Box::new(to.clone());
                    } else {
                        func_expr = Box::new(Expr::Literal(name1));
                    }

                    if name2 == from {
                        argu_expr = Box::new(to);
                    } else {
                        argu_expr = Box::new(Expr::Literal(name2));
                    }

                    return Expr::Application(ApplicationExpr {
                        func_expr,
                        argu_expr,
                    });
                }
            } else {
                let func_expr;
                let argu_expr;
                if name1 == from {
                    func_expr = Box::new(to.clone());
                } else {
                    func_expr = Box::new(Expr::Literal(name1));
                }

                if name2 == from {
                    argu_expr = Box::new(to);
                } else {
                    argu_expr = Box::new(Expr::Literal(name2));
                }

                return Expr::Application(ApplicationExpr {
                    func_expr,
                    argu_expr,
                });
            }
        }
        (Literal(func_expr), Function(argu_expr)) => {
            let inner_para = argu_expr.clone().parameter;
            if inner_para != *scope {
                let result = beta_reduction_in_func(from.clone(), to.clone(), argu_expr);
                if func_expr == from {
                    return Expr::Application(ApplicationExpr {
                        func_expr: Box::new(to),
                        argu_expr: Box::new(result),
                    });
                } else {
                    return Expr::Application(ApplicationExpr {
                        func_expr: Box::new(Expr::Literal(func_expr)),
                        argu_expr: Box::new(result),
                    });
                }
            } else {
                //内层形参覆盖外层形参,这意味着不替换了argu_expr
                if func_expr == from {
                    return Expr::Application(ApplicationExpr {
                        func_expr: Box::new(to),
                        argu_expr: Box::new(Expr::Function(argu_expr)),
                    });
                } else {
                    return Expr::Application(expr);
                }
            }
        }
        (Literal(func_expr), Application(argu_expr)) => {
            let result = beta_reduction_in_app(from.clone(), to.clone(), argu_expr, scope);
            if func_expr == from {
                return Expr::Application(ApplicationExpr {
                    func_expr: Box::new(to),
                    argu_expr: Box::new(result),
                });
            } else {
                return Expr::Application(ApplicationExpr {
                    func_expr: Box::new(Expr::Literal(func_expr)),
                    argu_expr: Box::new(result),
                });
            }
        }
        (Function(func_expr), Literal(argu_expr)) => {
            let inner_para = func_expr.clone().parameter;
            if inner_para != *scope {
                let result = beta_reduction_in_func(from.clone(), to.clone(), func_expr);
                if argu_expr == from {
                    return Expr::Application(ApplicationExpr {
                        func_expr: Box::new(result),
                        argu_expr: Box::new(to),
                    });
                } else {
                    return Expr::Application(ApplicationExpr {
                        func_expr: Box::new(result),
                        argu_expr: Box::new(Expr::Literal(argu_expr)),
                    });
                }
            } else {
                //内层形参覆盖外层形参,这意味着不替换了argu_expr
                if argu_expr == from {
                    return Expr::Application(ApplicationExpr {
                        func_expr: Box::new(Expr::Function(func_expr)),
                        argu_expr: Box::new(to),
                    });
                } else {
                    return Expr::Application(expr);
                }
            }
        }
        (Application(func_expr), Literal(argu_expr)) => {
            let result = beta_reduction_in_app(from.clone(), to.clone(), func_expr, scope);
            if argu_expr == from {
                return Expr::Application(ApplicationExpr {
                    func_expr: Box::new(result),
                    argu_expr: Box::new(to),
                });
            } else {
                return Expr::Application(ApplicationExpr {
                    func_expr: Box::new(result),
                    argu_expr: Box::new(Expr::Literal(argu_expr)),
                });
            }
        }
        (Function(func_expr), Function(argu_expr)) => {
            let func_inner_para = func_expr.clone().parameter;
            let argu_inner_para = argu_expr.clone().parameter;
            let new_func_expr;
            let new_argu_expr;
            if func_inner_para != *scope {
                new_func_expr = beta_reduction_in_func(from.clone(), to.clone(), func_expr);
            } else {
                //内层形参覆盖外层形参
                new_func_expr = Expr::Function(func_expr);
            }
            if argu_inner_para != *scope {
                new_argu_expr = beta_reduction_in_func(from.clone(), to.clone(), argu_expr);
            } else {
                //内层形参覆盖外层形参
                new_argu_expr = Expr::Function(argu_expr);
            }

            return Expr::Application(ApplicationExpr {
                func_expr: Box::new(new_func_expr),
                argu_expr: Box::new(new_argu_expr),
            });
        }
        (Function(func_expr), Application(argu_expr)) => {
            let func_inner_para = func_expr.clone().parameter;
            let new_func_expr;
            if func_inner_para != *scope {
                new_func_expr = beta_reduction_in_func(from.clone(), to.clone(), func_expr);
            } else {
                new_func_expr = Expr::Function(func_expr);
            }

            let argu_expr_replaced =
                beta_reduction_in_app(from.clone(), to.clone(), argu_expr, scope);
            return Expr::Application(ApplicationExpr {
                func_expr: Box::new(new_func_expr),
                argu_expr: Box::new(argu_expr_replaced),
            });
        }
        (Application(func_expr), Function(argu_expr)) => {
            let func_expr_replaced =
                beta_reduction_in_app(from.clone(), to.clone(), func_expr, scope);
            let argu_inner_para = argu_expr.clone().parameter;
            let new_argu_expr;
            if argu_inner_para != *scope {
                new_argu_expr = beta_reduction_in_func(from.clone(), to.clone(), argu_expr);
            } else {
                //内层形参覆盖外层形参
                new_argu_expr = Expr::Function(argu_expr);
            }

            return Expr::Application(ApplicationExpr {
                func_expr: Box::new(func_expr_replaced),
                argu_expr: Box::new(new_argu_expr),
            });
        }
        (Application(func_expr), Application(argu_expr)) => {
            let func_expr_replaced =
                beta_reduction_in_app(from.clone(), to.clone(), func_expr, scope);
            let argu_expr_replaced =
                beta_reduction_in_app(from.clone(), to.clone(), argu_expr, scope);
            return Expr::Application(ApplicationExpr {
                func_expr: Box::new(func_expr_replaced),
                argu_expr: Box::new(argu_expr_replaced),
            });
        }
    }
}

fn rename_formal_para_app(from: String, to: String, expr: ApplicationExpr) -> ApplicationExpr {
    let func_expr = expr.func_expr;
    let argu_expr = expr.argu_expr;

    let func_expr_replaced = Box::new(rename_formal_para(from.clone(), to.clone(), *func_expr));
    let argu_expr_replaced = Box::new(rename_formal_para(from, to, *argu_expr));

    return ApplicationExpr {
        func_expr: func_expr_replaced,
        argu_expr: argu_expr_replaced,
    };
}

fn rename_formal_para(from: String, to: String, expr: Expr) -> Expr {
    let func_expr_replaced = match expr {
        Literal(name) => {
            if name == from {
                Expr::Literal(to.clone())
            } else {
                Expr::Literal(name)
            }
        }
        Function(function_expr) => Expr::Function(rename_formal_para_func(from, to, function_expr)),
        Application(application_expr) => {
            Expr::Application(rename_formal_para_app(from, to, application_expr))
        }
    };
    return func_expr_replaced;
}

fn rename_formal_para_func(from: String, to: String, expr: FunctionExpr) -> FunctionExpr {
    let para = expr.parameter;
    let body = expr.body;
    FunctionExpr {
        parameter: para,
        body: Box::new(rename_formal_para(from, to, *body)),
    }
}

fn replace_func_expr_app(to: FunctionExpr, expr: ApplicationExpr) -> ApplicationExpr {
    ApplicationExpr {
        func_expr: Box::new(Expr::Function(to)),
        argu_expr: expr.argu_expr,
    }
}

fn expr_to_string(expr: Expr) -> String {
    let expr_string = match expr {
        Literal(name) => name,
        Function(function_expr) => expr_to_string_func(function_expr),
        Application(application_expr) => expr_to_string_app(application_expr),
    };
    return expr_string;
}

fn expr_to_string_app(expr: ApplicationExpr) -> String {
    let func_expr = expr.func_expr;
    let argu_expr = expr.argu_expr;

    let func_expr_to_string = expr_to_string(*func_expr);
    let argu_expr_to_string = expr_to_string(*argu_expr);

    return format!("({func_expr_to_string} {argu_expr_to_string})");
}

fn expr_to_string_func(expr: FunctionExpr) -> String {
    let para = expr.parameter;
    let body = expr.body;
    let body_to_string = expr_to_string(*body);

    return format!("λ{para}.{body_to_string}");
}

#[cfg(test)]
mod interpreter_tests {}
