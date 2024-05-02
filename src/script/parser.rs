use chumsky::prelude::*;
use std::fmt::Display;

pub(super) type Block = Vec<Statement>;

#[derive(Debug, PartialEq, Clone)]
pub(super) struct Variable(String, Option<Box<Variable>>); // variable with zero or more attribute accesses

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = format!("#{}", self.0);
        if let Some(ref v) = self.1 {
            s.push_str(&v.to_string());
        }

        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone)]
pub(super) enum Expression {
    ReferenceDeclaration(Box<Expression>, Box<Expression>),
    ValueDeclaration(Box<Expression>, Box<Expression>),
    FunctionCall(String, Vec<Expression>),
    MethodCall(Box<Expression>, String, Vec<Expression>),
    FunctionDefinition(Vec<String>, Block),
    Variable(Variable),
    String(String),
    Int(i32),
    Float(f32),
    Global(Box<Expression>),
}

#[derive(Debug, Clone)]
pub(super) struct Conditional(Expression, Block, Option<Box<Conditional>>); // if condition with zero or more else-ifs

#[derive(Debug, Clone)]
pub(super) enum Statement {
    ObjectInitialization(Expression, Block),
    Conditional(Conditional, Option<Block>), // conditional with an optional else block
    Expression(Expression),
    Return,
    // TODO: loops and breaks
}

pub(super) fn parser<'src>(
) -> impl Parser<'src, &'src str, Block, extra::Err<Rich<'src, char, SimpleSpan<usize>>>> {
    let int = text::int(10).from_str().unwrapped().map(Expression::Int);

    let float = text::int(10)
        .then(just('.'))
        .then(text::int(10))
        .to_slice()
        .from_str()
        .unwrapped()
        .map(Expression::Float);

    let num = float.or(int);

    // I'm pretty sure the minus sign isn't an operator but rather directly part of the number
    // parsing logic
    let neg_num = just('-').ignore_then(num).map(|e| match e {
        Expression::Int(i) => Expression::Int(-i),
        Expression::Float(f) => Expression::Float(-f),
        _ => unreachable!(),
    });

    let string = just('"')
        .ignore_then(none_of('"').repeated().collect()) // as far as I know, escapes aren't supported
        .then_ignore(just('"'))
        .map(Expression::String);

    let var = recursive(|var| {
        just('#').ignore_then(text::ident()).then(var.or_not()).map(
            |(v, a): (&str, Option<Expression>)| {
                Expression::Variable(Variable(
                    String::from(v),
                    a.map(|e| match e {
                        Expression::Variable(v) => Box::new(v),
                        _ => unreachable!(),
                    }),
                ))
            },
        )
    });

    // slightly redundant global parsing to reduce recursion in expressions
    let global_var = just('$')
        .padded()
        .repeated()
        .at_least(1)
        .count()
        .then(var.clone())
        .map(|(g, v)| {
            let mut out = Expression::Global(Box::new(v));
            for _ in 0..g - 1 {
                out = Expression::Global(Box::new(out));
            }
            out
        });

    let any_var = global_var.or(var.clone());

    let atom = var.or(string).or(neg_num).or(num);

    let stmt = recursive(|stmt| {
        let block = stmt.repeated().collect().delimited_by(just('{'), just('}'));

        let expr = recursive(|expr| {
            let args = expr.clone().separated_by(just(',')).collect();

            // https://github.com/zesterer/chumsky/discussions/58
            // if we let the left-hand side of a method call be any expression, we get infinite recursion
            // and a stack overflow
            let delimited = atom
                .clone()
                .or(expr.clone().delimited_by(just('('), just(')')));
            let method = delimited
                .then(text::ident().padded())
                .then(args.clone())
                .map(|((o, m), a): ((Expression, &str), Vec<Expression>)| {
                    Expression::MethodCall(Box::new(o), String::from(m), a)
                });

            let ref_decl = any_var
                .clone()
                .then_ignore(just('|').padded())
                .then(expr.clone())
                .map(|(l, r)| Expression::ReferenceDeclaration(Box::new(l), Box::new(r)));

            let val_decl = any_var
                .then_ignore(just(':').padded())
                .then(expr.clone())
                .map(|(l, r)| Expression::ValueDeclaration(Box::new(l), Box::new(r)));

            let func_def = just("?F")
                .padded()
                .ignore_then(
                    text::ident()
                        .to_slice()
                        .map(String::from)
                        .padded()
                        .separated_by(just(','))
                        .collect()
                        .delimited_by(just('('), just(')'))
                        .padded()
                        .or_not(),
                )
                .then(block)
                .map(|(a, b)| Expression::FunctionDefinition(a.unwrap_or_else(Vec::new), b));

            let function =
                text::ident()
                    .padded()
                    .then(args)
                    .map(|(f, a): (&str, Vec<Expression>)| {
                        Expression::FunctionCall(String::from(f), a)
                    });

            let global = just('$')
                .padded()
                .ignore_then(expr.clone())
                .map(|e| Expression::Global(Box::new(e)));

            func_def
                .or(ref_decl)
                .or(val_decl)
                .or(global)
                .or(function)
                .or(method)
                .or(atom)
                .or(expr.delimited_by(just('('), just(')')))
                .padded()
        });

        expr.then_ignore(just(';'))
            .padded()
            .map(Statement::Expression)
    });

    stmt.repeated().collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn one_statement(text: &str) -> Statement {
        let parser = parser();
        let result = parser.parse(text).unwrap();
        result
            .into_iter()
            .next()
            .expect("at least one statement should be provided")
    }

    #[test]
    fn test_int() {
        let stmt = one_statement(" 4 ; ");
        assert!(matches!(stmt, Statement::Expression(Expression::Int(4))));
    }

    #[test]
    fn test_float() {
        let stmt = one_statement("1.3;");
        match stmt {
            Statement::Expression(Expression::Float(f)) => assert!((f - 1.3).abs() < f32::EPSILON),
            _ => panic!("Statement was not a float expression"),
        }
    }

    #[test]
    fn test_neg() {
        let stmt = one_statement("-17; ");
        assert!(matches!(stmt, Statement::Expression(Expression::Int(-17))));
    }

    #[test]
    fn test_string() {
        let stmt = one_statement("\"hello, world!\";");
        assert!(
            matches!(stmt, Statement::Expression(Expression::String(ref s)) if s == "hello, world!")
        );
    }

    #[test]
    fn test_variable() {
        let stmt = one_statement("#a#b;");
        let Statement::Expression(Expression::Variable(v)) = stmt else {
            panic!("Statement was not a variable expression");
        };
        let attr = v.1.as_ref().unwrap();

        assert_eq!(v.0, "a");
        assert_eq!(attr.0, "b");
        assert!(attr.1.is_none());
        assert_eq!(v.to_string(), "#a#b");
    }

    #[test]
    fn test_paren_scalar() {
        let stmt = one_statement("(5); ");
        assert!(matches!(stmt, Statement::Expression(Expression::Int(5))));
    }

    #[test]
    fn test_global_var() {
        let stmt = one_statement("$#a;");
        let Statement::Expression(Expression::Global(global)) = stmt else {
            panic!("Statement was not a global expression");
        };
        assert!(matches!(*global, Expression::Variable(Variable(ref s, None)) if s == "a"));
    }

    #[test]
    fn test_method_call() {
        let stmt = one_statement("#object method 1, 2;");
        let Statement::Expression(Expression::MethodCall(obj, method, args)) = stmt else {
            panic!("Statement was not a global expression");
        };
        assert!(matches!(*obj, Expression::Variable(Variable(ref s, None)) if s == "object"));
        assert_eq!(method, "method");
        assert_eq!(args.len(), 2);
        let mut it = args.into_iter();
        assert!(matches!(it.next().unwrap(), Expression::Int(1)));
        assert!(matches!(it.next().unwrap(), Expression::Int(2)));
    }

    #[test]
    fn test_function_call() {
        let stmt = one_statement("Function;");
        assert!(
            matches!(stmt, Statement::Expression(Expression::FunctionCall(ref s, ref a)) if s == "Function" && a.is_empty())
        );
    }

    #[test]
    fn test_ref_assign() {
        let stmt = one_statement("#ab | 4;");
        let Statement::Expression(Expression::ReferenceDeclaration(var, value)) = stmt else {
            panic!("Statement was not a reference declaration expression");
        };
        assert!(matches!(*var, Expression::Variable(Variable(ref s, None)) if s == "ab"));
        assert!(matches!(*value, Expression::Int(4)));
    }

    #[test]
    fn test_val_assign() {
        let stmt = one_statement("#ba : 5;");
        let Statement::Expression(Expression::ValueDeclaration(var, value)) = stmt else {
            panic!("Statement was not a value declaration expression");
        };
        assert!(matches!(*var, Expression::Variable(Variable(ref s, None)) if s == "ba"));
        assert!(matches!(*value, Expression::Int(5)));
    }

    #[test]
    fn test_global_literal() {
        let stmt = one_statement("$(4);");
        let Statement::Expression(Expression::Global(value)) = stmt else {
            panic!("Statement was not a value declaration expression");
        };
        assert!(matches!(*value, Expression::Int(4)));
    }

    #[test]
    fn test_func_no_args() {
        let stmt = one_statement(
            "
        #MyFunc | ?F {
            $Print \"my cool function\";
        };
        ",
        );
        let Statement::Expression(Expression::ReferenceDeclaration(var, value)) = stmt else {
            panic!("Statement was not a reference declaration expression");
        };
        assert!(matches!(*var, Expression::Variable(Variable(ref s, None)) if s == "MyFunc"));
        let Expression::FunctionDefinition(args, body) = *value else {
            panic!("Value was not a function definition");
        };
        assert!(args.is_empty());
        assert_eq!(body.len(), 1);
    }

    #[test]
    fn test_func_args() {
        let stmt = one_statement(
            "
        ?F (a, b) {
            #a add #b;
        };",
        );
        let Statement::Expression(Expression::FunctionDefinition(args, body)) = stmt else {
            panic!("Value was not a function definition");
        };
        assert_eq!(args.len(), 2);
        assert_eq!(args[0], "a");
        assert_eq!(args[1], "b");
        assert_eq!(body.len(), 1);
    }
}
