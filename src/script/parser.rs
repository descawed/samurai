use std::fmt::{Display, Formatter};
use std::ops::{Deref, DerefMut};

use chumsky::prelude::*;

#[derive(Debug, Clone)]
pub(super) struct Block(Vec<Statement>);

impl Display for Block {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.is_empty() {
            write!(f, "{{ }}")
        } else {
            write!(f, "{{\n")?;
            for stmt in self {
                // for proper indentation, we need to first write the statement to a temp
                // string, as statements can contain multiple lines and nested blocks
                let stmt_string = stmt.to_string();
                write!(f, "\t{}\n", stmt_string.replace('\n', "\n\t"))?;
            }
            write!(f, "}}")
        }
    }
}

//#region Vec wrapper impls for Block
impl From<Vec<Statement>> for Block {
    fn from(value: Vec<Statement>) -> Self {
        Self(value)
    }
}

impl Deref for Block {
    type Target = Vec<Statement>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Block {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl IntoIterator for Block {
    type Item = Statement;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> IntoIterator for &'a Block {
    type Item = &'a Statement;
    type IntoIter = std::slice::Iter<'a, Statement>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a> IntoIterator for &'a mut Block {
    type Item = &'a mut Statement;
    type IntoIter = std::slice::IterMut<'a, Statement>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}
//#endregion

#[derive(Debug, PartialEq, Clone)]
pub(super) struct Variable(String, Option<Box<Variable>>); // variable with zero or more attribute accesses

impl Display for Variable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.0)?;
        if let Some(ref v) = self.1 {
            v.fmt(f)?;
        }

        Ok(())
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

impl Expression {
    pub fn declaration(&self) -> Option<(&Self, &Self)> {
        match self {
            Self::ReferenceDeclaration(lhs, rhs) | Self::ValueDeclaration(lhs, rhs) => {
                Some((lhs.as_ref(), rhs.as_ref()))
            }
            _ => None,
        }
    }

    pub fn is_atom(&self) -> bool {
        match self {
            Self::Int(_) | Self::Float(_) | Self::String(_) | Self::Variable(_) => true,
            Self::Global(e) => e.is_atom(),
            _ => false,
        }
    }

    fn write_safe(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.is_atom() {
            write!(f, "{}", self)
        } else {
            write!(f, "({})", self)
        }
    }

    fn write_arg_list(args: &[Self], f: &mut Formatter<'_>) -> std::fmt::Result {
        if !args.is_empty() {
            write!(f, " ")?;
            let mut is_first = true;
            for arg in args {
                if !is_first {
                    write!(f, ", ")?;
                }
                is_first = false;

                arg.write_safe(f)?;
            }
        }
        Ok(())
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ReferenceDeclaration(lhs, rhs) => write!(f, "{} | {}", lhs, rhs),
            Self::ValueDeclaration(lhs, rhs) => write!(f, "{} : {}", lhs, rhs),
            Self::FunctionCall(name, args) => {
                write!(f, "{}", name)?;
                Self::write_arg_list(args, f)
            }
            Self::MethodCall(obj, method, args) => {
                obj.write_safe(f)?;
                write!(f, " {}", method)?;
                Self::write_arg_list(args, f)
            }
            Self::FunctionDefinition(args, body) => {
                write!(f, "?F")?;
                if !args.is_empty() {
                    write!(f, "( ")?;
                    let mut is_first = true;
                    for arg in args {
                        if !is_first {
                            write!(f, ", ")?;
                        }
                        is_first = false;

                        write!(f, "{}", arg)?;
                    }
                    write!(f, " )")?;
                }

                write!(f, " {}", body)
            }
            Self::Variable(v) => v.fmt(f),
            Self::String(s) => write!(f, "\"{}\"", s),
            Self::Int(i) => i.fmt(f),
            Self::Float(n) => n.fmt(f),
            Self::Global(e) => write!(f, "${}", e),
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct Conditional(Expression, Block, Option<Box<Conditional>>); // if condition with zero or more else-ifs

impl Display for Conditional {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}) {}", self.0, self.1)?;
        if let Some(ref elseif) = self.2 {
            write!(f, " {}", *elseif)?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub(super) enum Statement {
    ObjectInitialization(Expression, Block),
    Conditional(Conditional, Option<Block>), // conditional with an optional else block
    Expression(Expression),
    Return,
    // TODO: loops, breaks, ternary
}

impl Display for Statement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ObjectInitialization(obj, block) => {
                obj.write_safe(f)?;
                write!(f, " @{}", block)?;
            }
            Self::Conditional(conditional, else_block) => {
                write!(f, "?i {}", conditional)?;
                if let Some(block) = else_block {
                    write!(f, " {}", block)?;
                }
            }
            Self::Expression(expr) => expr.fmt(f)?,
            Self::Return => write!(f, "/return")?,
        }

        write!(f, ";")
    }
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

    let any_var = global_var.or(var.clone()).padded();

    let atom = var.or(string).or(neg_num).or(num);

    let stmt = recursive(|stmt| {
        let block = stmt
            .repeated()
            .collect::<Vec<_>>()
            .delimited_by(just('{'), just('}'))
            .padded();

        let expr = recursive(|expr| {
            let args = expr.clone().separated_by(just(',')).collect();

            // https://github.com/zesterer/chumsky/discussions/58
            // if we let the left-hand side of a method call be any expression, we get infinite recursion
            // and a stack overflow, so limit it to a bare atom or a parenthetical expression.
            // a consequence of using atom here, which doesn't include global_var, is that we'll never
            // parse a method call as having a global variable on the left-hand side; it'll always be
            // the method call itself that's wrapped in a global context
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
                .then_ignore(just('|'))
                .then(expr.clone())
                .map(|(l, r)| Expression::ReferenceDeclaration(Box::new(l), Box::new(r)));

            let val_decl = any_var
                .then_ignore(just(':'))
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
                .then(block.clone())
                .map(|(a, b)| Expression::FunctionDefinition(a.unwrap_or_else(Vec::new), b.into()));

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

        let condition_block = recursive(|condition_block| {
            expr.clone()
                .delimited_by(just('('), just(')'))
                .then(block.clone())
                .then(condition_block.or_not())
                .map(|((c, b), e): ((Expression, Vec<_>), Option<Conditional>)| {
                    Conditional(c, b.into(), e.map(Box::new))
                })
        });
        let conditional = just("?i")
            .padded()
            .ignore_then(condition_block)
            .then(block.clone().or_not())
            .map(|(c, b)| Statement::Conditional(c, b.map(Block)));

        let object_init = expr
            .clone()
            .then_ignore(just('@'))
            .then(block)
            .map(|(e, b)| Statement::ObjectInitialization(e, b.into()));

        let return_stmt = just("/return").padded().to(Statement::Return);

        let stmt_expr = expr.map(Statement::Expression);

        conditional
            .or(return_stmt)
            .or(object_init)
            .or(stmt_expr)
            .then_ignore(just(';').padded())
    });

    stmt.repeated().collect().map(Block)
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

    #[test]
    fn test_if() {
        let stmt = one_statement(
            "
        ?i (#a eq 1) {
            Func1;
        };
        ",
        );
        let Statement::Conditional(conditional, None) = stmt else {
            panic!("Statement was not an if statement with no else");
        };
        assert!(matches!(conditional.0, Expression::MethodCall(_, _, _)));
        assert_eq!(conditional.1.len(), 1);
        assert!(conditional.2.is_none());
    }

    #[test]
    fn test_else_if() {
        let stmt = one_statement(
            "
        ?i (#a eq 1) {
            Func1;
        } (#a eq 2) {
            Func2;
            Func2_2;
        };
        ",
        );
        let Statement::Conditional(conditional, None) = stmt else {
            panic!("Statement was not an if statement with no else");
        };
        assert!(matches!(conditional.0, Expression::MethodCall(_, _, _)));
        assert_eq!(conditional.1.len(), 1);
        let Conditional(else_if_condition, else_if_block, None) =
            *conditional.2.expect("statement should have else-if")
        else {
            panic!("Statement was not an if statement with a single else-if");
        };
        assert!(matches!(else_if_condition, Expression::MethodCall(_, _, _)));
        assert_eq!(else_if_block.len(), 2);
    }

    #[test]
    fn test_else() {
        let stmt = one_statement(
            "
        ?i (#a eq 1) {
            Func1;
        } {
            Func2;
            Func2_2;
        };
        ",
        );
        let Statement::Conditional(conditional, Some(else_block)) = stmt else {
            panic!("Statement was not an if statement with an else");
        };
        assert!(matches!(conditional.0, Expression::MethodCall(_, _, _)));
        assert_eq!(conditional.1.len(), 1);
        assert!(conditional.2.is_none());
        assert_eq!(else_block.len(), 2);
    }

    #[test]
    fn test_else_if_else() {
        let stmt = one_statement(
            "
        ?i (#a eq 1) {
            Func1;
        } (#a eq 2) {
            Func2;
            Func2_2;
        } {
            Func3;
        };
        ",
        );
        let Statement::Conditional(conditional, Some(else_block)) = stmt else {
            panic!("Statement was not an if statement with an else");
        };
        assert!(matches!(conditional.0, Expression::MethodCall(_, _, _)));
        assert_eq!(conditional.1.len(), 1);
        let Conditional(else_if_condition, else_if_block, None) =
            *conditional.2.expect("statement should have else-if")
        else {
            panic!("Statement was not an if statement with a single else-if");
        };
        assert!(matches!(else_if_condition, Expression::MethodCall(_, _, _)));
        assert_eq!(else_if_block.len(), 2);
        assert_eq!(else_block.len(), 1);
    }

    #[test]
    fn test_object_init() {
        let stmt = one_statement(
            "
        (#MyClass : #object) @ {
            #attr : 1;
        };
        ",
        );
        let Statement::ObjectInitialization(obj_expr, block) = stmt else {
            panic!("Statement was not an object initialization statement");
        };
        let Expression::ValueDeclaration(class_var, super_var) = obj_expr else {
            panic!("Object expression was not a value declaration");
        };
        assert!(
            matches!(*class_var, Expression::Variable(Variable(ref s, None)) if s == "MyClass")
        );
        assert!(matches!(*super_var, Expression::Variable(Variable(ref s, None)) if s == "object"));
        assert_eq!(block.len(), 1);
    }

    #[test]
    fn test_return() {
        let stmt = one_statement(" /return ; ");
        assert!(matches!(stmt, Statement::Return));
    }

    #[test]
    fn test_round_trip() {
        let script = "\
(#MyClass : #object) @{
\t#a | 4;
\t#b : 2.3;
\t$GlobalFunc \"arg\";
\t?i (1) {
\t\t#c method;
\t} {
\t\tOtherFunc;
\t};
};";
        let stmt = one_statement(script);
        let formatted = stmt.to_string();
        assert_eq!(formatted, script);
    }
}
