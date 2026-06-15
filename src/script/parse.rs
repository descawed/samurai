use std::fmt::{Display, Formatter};
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

use anyhow::{Result, anyhow};
use chumsky::prelude::*;
use itertools::Itertools;

use super::types::{Scope, SharedScope, Variable};

const IDENTIFIER_CHARACTERS: &str =
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_";

#[derive(Debug, Clone)]
pub(super) struct Block(Vec<Statement>, Option<SharedScope>);

impl Block {
    /// Convert a top-level block to a string
    ///
    /// As opposed to the normal to_string, this doesn't include braces or any indentation.
    pub fn to_string_top_level(&self) -> String {
        self.0.iter().join("\n")
    }

    pub fn scope(&self) -> Option<SharedScope> {
        self.1.as_ref().map(Rc::clone)
    }

    pub fn set_scope(&mut self, scope: SharedScope) {
        self.1 = Some(scope);
    }

    pub fn ensure_scope(&mut self, parent: SharedScope) -> SharedScope {
        match &self.1 {
            Some(scope) => scope.borrow_mut().set_parent(parent),
            None => self.1 = Some(Scope::new(Some(parent))),
        }
        Rc::clone(self.1.as_ref().unwrap())
    }
}

impl Display for Block {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.is_empty() {
            write!(f, "{{ }}")
        } else {
            writeln!(f, "{{")?;
            for stmt in self {
                // for proper indentation, we need to first write the statement to a temp
                // string, as statements can contain multiple lines and nested blocks
                let stmt_string = stmt.to_string();
                writeln!(f, "\t{}", stmt_string.replace('\n', "\n\t"))?;
            }
            write!(f, "}}")
        }
    }
}

//#region Vec wrapper impls for Block
impl From<Vec<Statement>> for Block {
    fn from(value: Vec<Statement>) -> Self {
        Self(value, None)
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

/// The keyword form a function definition was written with.
///
/// Most definitions use `?F`, but a handful in the shipped scripts use a bare `?` or omit the
/// keyword entirely. We remember the original form so the formatter can reproduce it verbatim.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FuncKeyword {
    Full, // ?F
    Bare, // ?
    None, // no keyword at all
}

/// A parameter in a function definition.
///
/// Parameters are matched against body variables by their bare [`name`](Self::name), so the
/// leading `#` sigil (when present) is tracked separately rather than baked into the name.
#[derive(Debug, Clone)]
pub(super) struct Param {
    sigil: bool,
    name: String,
}

impl Param {
    /// The parameter's bare name, without any leading `#` sigil.
    pub fn as_str(&self) -> &str {
        &self.name
    }
}

impl Display for Param {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.sigil {
            write!(f, "#")?;
        }
        f.write_str(&self.name)
    }
}

/// An argument list for a function or method call.
///
/// Wraps the argument expressions but also records how many commas appeared before each argument
/// and after the last one. This lets the formatter reproduce unusual but syntactically-significant
/// comma patterns found in the shipped scripts (leading commas, doubled commas, trailing commas).
/// It derefs to the underlying `Vec<Expression>`, so analysis code can treat it as a plain list;
/// the comma metadata is only consulted by the formatter.
#[derive(Debug, Clone)]
pub(super) struct Args {
    values: Vec<Expression>,
    /// Number of commas appearing immediately before each argument. `commas_before[0]` is the
    /// count of leading commas before the first argument (normally 0); each subsequent entry is
    /// the number of commas separating an argument from its predecessor (normally 1). Always the
    /// same length as `values`.
    commas_before: Vec<usize>,
    /// Number of trailing commas after the final argument.
    trailing_commas: usize,
}

impl Args {
    pub fn new(values: Vec<Expression>, commas_before: Vec<usize>, trailing_commas: usize) -> Self {
        debug_assert_eq!(values.len(), commas_before.len());
        Self {
            values,
            commas_before,
            trailing_commas,
        }
    }
}

impl Deref for Args {
    type Target = Vec<Expression>;

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl DerefMut for Args {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.values
    }
}

impl IntoIterator for Args {
    type Item = Expression;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.values.into_iter()
    }
}

impl<'a> IntoIterator for &'a Args {
    type Item = &'a Expression;
    type IntoIter = std::slice::Iter<'a, Expression>;

    fn into_iter(self) -> Self::IntoIter {
        self.values.iter()
    }
}

impl<'a> IntoIterator for &'a mut Args {
    type Item = &'a mut Expression;
    type IntoIter = std::slice::IterMut<'a, Expression>;

    fn into_iter(self) -> Self::IntoIter {
        self.values.iter_mut()
    }
}

#[derive(Debug, Clone)]
pub(super) enum Expression {
    ReferenceDeclaration(Box<Expression>, Box<Expression>),
    ValueDeclaration(Box<Expression>, Box<Expression>),
    FunctionCall(String, Args),
    MethodCall(Box<Expression>, String, Args),
    FunctionDefinition(FuncKeyword, Vec<Param>, Block),
    TernaryConditional(Box<Expression>, Box<Expression>, Box<Expression>),
    Variable(Variable),
    String(String),
    Int(i32),
    Float(f32),
    Global(Box<Expression>),
}

impl Expression {
    pub fn new_var(name: String) -> Self {
        Self::Variable(Variable(name, None))
    }

    pub fn into_declaration(self) -> Option<(Self, Self)> {
        match self {
            Self::ReferenceDeclaration(lhs, rhs) | Self::ValueDeclaration(lhs, rhs) => {
                Some((*lhs, *rhs))
            }
            Self::Global(e) => e.into_declaration(),
            _ => None,
        }
    }

    pub fn declaration_mut(&mut self) -> Option<(&mut Self, &mut Self)> {
        match self {
            Self::ReferenceDeclaration(lhs, rhs) | Self::ValueDeclaration(lhs, rhs) => {
                Some((lhs.as_mut(), rhs.as_mut()))
            }
            Self::Global(e) => e.declaration_mut(),
            _ => None,
        }
    }

    pub fn inner_blocks_mut(&mut self) -> Vec<(&mut [Param], &mut Block)> {
        match self {
            Expression::ReferenceDeclaration(_, rhs) | Expression::ValueDeclaration(_, rhs) => {
                rhs.inner_blocks_mut()
            }
            // I don't know if there's any situation where passing a function definition as an argument makes sense, but we'll support it anyway
            Expression::FunctionCall(_, args) | Expression::MethodCall(_, _, args) => args
                .iter_mut()
                .flat_map(|a| a.inner_blocks_mut().into_iter())
                .collect(),
            Expression::FunctionDefinition(_, args, block) => vec![(args, block)],
            Expression::Global(e) => e.inner_blocks_mut(),
            _ => vec![],
        }
    }

    pub fn walk_mut<F: FnMut(&mut Self)>(&mut self, f: &mut F) {
        match self {
            Expression::ReferenceDeclaration(lhs, rhs) | Expression::ValueDeclaration(lhs, rhs) => {
                f(lhs);
                lhs.walk_mut(f);
                f(rhs);
                rhs.walk_mut(f);
            }
            Expression::FunctionCall(_, args) => {
                for arg in args {
                    f(arg);
                    arg.walk_mut(f);
                }
            }
            Expression::MethodCall(obj, _, args) => {
                f(obj);
                obj.walk_mut(f);
                for arg in args {
                    f(arg);
                    arg.walk_mut(f);
                }
            }
            Expression::TernaryConditional(cond, if_true, if_false) => {
                f(cond);
                cond.walk_mut(f);
                f(if_true);
                if_true.walk_mut(f);
                f(if_false);
                if_false.walk_mut(f);
            }
            Expression::Global(e) => {
                f(e);
                e.walk_mut(f);
            }
            _ => (),
        }
    }

    pub fn unwrap_global(&self) -> (&Self, bool) {
        match self {
            Self::Global(e) => (e.unwrap_global().0, true),
            _ => (self, false),
        }
    }

    pub fn unwrap_global_mut(&mut self) -> (&mut Self, bool) {
        match self {
            Self::Global(e) => (e.unwrap_global_mut().0, true),
            _ => (self, false),
        }
    }

    pub fn is_atom(&self) -> bool {
        match self {
            Self::Int(_) | Self::Float(_) | Self::String(_) | Self::Variable(_) => true,
            Self::FunctionCall(_, args) => args.is_empty(), // don't need parentheses around a function call with no args
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

    fn write_arg_list(args: &Args, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (i, arg) in args.values.iter().enumerate() {
            let commas = args.commas_before[i];
            if i == 0 && commas == 0 {
                // ordinary case: a single space separates the callee from its first argument
                write!(f, " ")?;
            } else {
                // any commas (a leading comma before the first argument, or the separators
                // between arguments) render with no space before and one space after
                for _ in 0..commas {
                    write!(f, ", ")?;
                }
            }

            arg.write_safe(f)?;
        }

        for _ in 0..args.trailing_commas {
            write!(f, ", ")?;
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
                // as a convention, list definitions are always in parentheses
                let is_list = name == "list";
                if is_list {
                    write!(f, "(")?;
                }
                write!(f, "{}", name)?;
                Self::write_arg_list(args, f)?;
                if is_list {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Self::MethodCall(obj, method, args) => {
                obj.write_safe(f)?;
                write!(f, " {}", method)?;
                Self::write_arg_list(args, f)
            }
            Self::FunctionDefinition(keyword, args, body) => {
                let mut need_space = match keyword {
                    FuncKeyword::Full => {
                        write!(f, "?F")?;
                        true
                    }
                    FuncKeyword::Bare => {
                        write!(f, "?")?;
                        true
                    }
                    FuncKeyword::None => false,
                };

                if !args.is_empty() {
                    if need_space {
                        write!(f, " ")?;
                    }
                    write!(f, "(")?;
                    let mut is_first = true;
                    for arg in args {
                        if !is_first {
                            write!(f, ", ")?;
                        }
                        is_first = false;

                        write!(f, "{}", arg)?;
                    }
                    write!(f, ")")?;
                    need_space = true;
                }

                if need_space {
                    write!(f, " ")?;
                }
                write!(f, "{}", body)
            }
            Self::TernaryConditional(cond, if_true, if_false) => {
                write!(f, "?I ")?;
                cond.write_safe(f)?;
                write!(f, ", ")?;
                if_true.write_safe(f)?;
                write!(f, ", ")?;
                if_false.write_safe(f)
            }
            Self::Variable(v) => v.fmt(f),
            Self::String(s) => write!(f, "\"{}\"", s),
            Self::Int(i) => i.fmt(f),
            Self::Float(n) => write!(f, "{:?}", n), // debug format so we don't format whole numbers like ints
            Self::Global(e) => write!(f, "${}", e),
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct Conditional(pub Expression, pub Block, pub Option<Box<Conditional>>); // if condition with zero or more else-ifs

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
    WhileLoop(Expression, Block),
    Return,
    Break,
    Empty,
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
            Self::WhileLoop(expr, block) => {
                write!(f, "?W {{ ({}) }}, {}", expr, block)?;
            }
            Self::Return => write!(f, "/return")?,
            Self::Break => write!(f, "/break")?,
            Self::Empty => {}
        }

        write!(f, ";")
    }
}

pub(super) fn parser<'src>()
-> impl Parser<'src, &'src str, Block, extra::Err<Rich<'src, char, SimpleSpan<usize>>>> {
    // padding that skips whitespace as well as `//` line comments, which run to the end of the
    // line. comments aren't represented in the AST; they're simply discarded like whitespace.
    let pad = {
        let comment = just("//")
            .then(any().and_is(just('\n').not()).repeated())
            .ignored();
        let whitespace = any().filter(|c: &char| c.is_whitespace()).ignored();
        whitespace.or(comment).repeated().ignored()
    };

    let int = text::digits(10)
        .to_slice()
        .from_str()
        .unwrapped()
        .map(Expression::Int);

    let float = text::digits(10)
        .then(just('.'))
        // need to use digits(10) instead of int(10) because otherwise we won't match a fractional
        // part that consists solely of multiple zeroes
        .then(text::digits(10))
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

    // FIXME: this isn't quite right. I've seen functions that reference their arguments with an
    //  identifier alone and no #. need more research.
    let var = recursive(|var| {
        just('#')
            .padded_by(pad.clone()) // at least one script has a variable usage with a space between the # and the identifier
            .ignore_then(
                one_of(IDENTIFIER_CHARACTERS)
                    .repeated()
                    .at_least(1)
                    .collect::<String>(),
            )
            .then(var.or_not())
            .map(|(v, a): (String, Option<Expression>)| {
                Expression::Variable(Variable(
                    v,
                    a.map(|e| match e {
                        Expression::Variable(v) => Box::new(v),
                        _ => unreachable!(),
                    }),
                ))
            })
    });

    // slightly redundant global parsing to reduce recursion in expressions
    let global_var = just('$')
        .padded_by(pad.clone())
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

    let any_var = global_var.or(var.clone()).padded_by(pad.clone());

    let atom = var.or(string).or(neg_num).or(num);

    let stmt = recursive(|stmt| {
        // I used to use delimited_by here, but that seemed to require at least one statement in the
        // block to parse correctly, and we need to support empty blocks
        let block = just('{')
            .padded_by(pad.clone())
            .ignore_then(stmt.repeated().collect::<Vec<_>>())
            .then_ignore(just('}').padded_by(pad.clone()))
            .padded_by(pad.clone());

        let expr = recursive(|expr| {
            // an argument list records how many commas surround each argument so the formatter can
            // reproduce the original (possibly irregular) comma usage. arguments must still be
            // separated by at least one comma, but we additionally allow leading commas (a comma
            // immediately after the callee), doubled commas between arguments, and trailing commas.
            let comma = just(',').padded_by(pad.clone());
            let args = comma
                .clone()
                .repeated()
                .count() // leading commas before the first argument
                .then(expr.clone())
                .then(
                    comma
                        .clone()
                        .repeated()
                        .at_least(1)
                        .count() // separator commas between arguments
                        .then(expr.clone())
                        .repeated()
                        .collect::<Vec<(usize, Expression)>>(),
                )
                .then(comma.repeated().count()) // trailing commas
                .map(|(((leading, first), rest), trailing)| {
                    let mut values = Vec::with_capacity(rest.len() + 1);
                    let mut commas_before = Vec::with_capacity(rest.len() + 1);
                    values.push(first);
                    commas_before.push(leading);
                    for (commas, arg) in rest {
                        values.push(arg);
                        commas_before.push(commas);
                    }
                    Args::new(values, commas_before, trailing)
                })
                .or_not()
                .map(|args| args.unwrap_or_else(|| Args::new(Vec::new(), Vec::new(), 0)));

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
                .then(text::ident().or(one_of("=<>").to_slice()).padded_by(pad.clone()))
                .then(args.clone())
                .map(|((o, m), a): ((Expression, &str), Args)| {
                    Expression::MethodCall(Box::new(o), String::from(m), a)
                });

            let ref_decl = any_var
                .clone()
                .then_ignore(just('|'))
                .then(expr.clone())
                .map(|(l, r)| Expression::ReferenceDeclaration(Box::new(l), Box::new(r)));

            let val_decl = any_var
                .clone()
                .then_ignore(just(':'))
                .then(expr.clone())
                .map(|(l, r)| Expression::ValueDeclaration(Box::new(l), Box::new(r)));

            let ternary = just("?I")
                .padded_by(pad.clone())
                .ignore_then(expr.clone())
                .then_ignore(just(',').padded_by(pad.clone()))
                .then(expr.clone())
                .then_ignore(just(',').padded_by(pad.clone()))
                .then(expr.clone())
                .map(|((c, t), f)| {
                    Expression::TernaryConditional(Box::new(c), Box::new(t), Box::new(f))
                });

            // a small number of scripts have function definitions that are lacking the ?F keyword,
            // and some have only a ? with no F. I don't know if this even works as intended
            // in-game, but for compatibility purposes, we'll parse it.
            // remember which keyword form the definition used so we can reproduce it. `?F` must be
            // tried before a bare `?` so the `F` isn't left dangling.
            let func_keyword = just("?F")
                .to(FuncKeyword::Full)
                .or(just('?').to(FuncKeyword::Bare))
                .or_not()
                .map(|k| k.unwrap_or(FuncKeyword::None));

            // a parameter name may carry a leading `#` sigil (which we preserve) and, unlike most
            // identifiers, may consist entirely of digits
            let param = just('#')
                .or_not()
                .map(|sigil| sigil.is_some())
                .then(
                    one_of(IDENTIFIER_CHARACTERS)
                        .repeated()
                        .at_least(1)
                        .collect::<String>(),
                )
                .map(|(sigil, name)| Param { sigil, name });

            let func_def = func_keyword
                .padded_by(pad.clone())
                .then(
                    param
                        .padded_by(pad.clone())
                        .separated_by(just(','))
                        .collect::<Vec<Param>>()
                        .delimited_by(just('('), just(')'))
                        .padded_by(pad.clone())
                        .or_not(),
                )
                .then(block.clone())
                .map(|((keyword, params), b)| {
                    Expression::FunctionDefinition(keyword, params.unwrap_or_default(), b.into())
                });

            let function =
                text::ident()
                    .padded_by(pad.clone())
                    .then(args)
                    .map(|(f, a): (&str, Args)| Expression::FunctionCall(String::from(f), a));

            let global = just('$')
                .padded_by(pad.clone())
                .ignore_then(expr.clone())
                .map(|e| Expression::Global(Box::new(e)));

            // if there's a syntax error in a declaration or method call, chumsky will back up and
            // look for an alternative valid parse. since a lone atom is a valid expression, that
            // parse will succeed, and the parser will then error on the subsequent assignment
            // operator or method name, obscuring the true source of the error. to prevent that,
            // we only allow parsing an atom if it's not part of a declaration or method call.
            let decl_or_method =
                any_var.then_ignore(text::ident().or(one_of("=<>|:").to_slice()).padded_by(pad.clone()));

            func_def
                .or(ref_decl)
                .or(val_decl)
                .or(global)
                .or(function)
                .or(ternary)
                .or(method)
                .or(atom.and_is(decl_or_method.not()))
                .or(expr.delimited_by(just('('), just(')')))
                .padded_by(pad.clone())
        });

        let semicolon = just(';').padded_by(pad.clone());

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
            .padded_by(pad.clone())
            .ignore_then(condition_block)
            .then(block.clone().or_not())
            .then_ignore(semicolon.or_not())
            .map(|(c, b)| Statement::Conditional(c, b.map(|b| Block(b, None))));

        let object_init = expr
            .clone()
            .then_ignore(just('@'))
            .then(block.clone())
            .then_ignore(semicolon.or_not())
            .map(|(e, b)| Statement::ObjectInitialization(e, b.into()));

        let while_loop = just("?W")
            .ignore_then(just('{').padded_by(pad.clone()))
            .ignore_then(expr.clone())
            .then_ignore(just('}').padded_by(pad.clone()))
            .then_ignore(just(',').padded_by(pad.clone()))
            .then(block)
            .then_ignore(semicolon.or_not())
            .map(|(e, b)| Statement::WhileLoop(e, b.into()));

        let return_stmt = just("/r")
            .then_ignore(text::ident().or_not())
            .padded_by(pad.clone())
            // the last statement in a block doesn't have to have a semicolon
            .then_ignore(semicolon.or(just('}').padded_by(pad.clone()).rewind()))
            .to(Statement::Return);

        let break_stmt = just("/b")
            .then_ignore(text::ident().or_not())
            .padded_by(pad.clone())
            // the last statement in a block doesn't have to have a semicolon
            .then_ignore(semicolon.or(just('}').padded_by(pad.clone()).rewind()))
            .to(Statement::Break);

        let stmt_expr = expr
            .then_ignore(semicolon.or(just('}').padded_by(pad.clone()).rewind()))
            .map(Statement::Expression);

        let empty_stmt = semicolon.to(Statement::Empty);

        conditional
            .or(return_stmt)
            .or(break_stmt)
            .or(object_init)
            .or(while_loop)
            .or(stmt_expr)
            .or(empty_stmt)
    });

    stmt.repeated()
        .collect()
        // pad the whole program so a script consisting only of comments/whitespace still parses
        .padded_by(pad.clone())
        .then_ignore(end())
        .map(|b| Block(b, None))
}

fn get_line_number(text: &str, index: usize) -> (usize, usize) {
    let fragment = &text[..index];
    let line_start = fragment.rfind('\n').unwrap_or(0);
    let line_num = fragment.matches('\n').count() + 1;
    (line_num, index - line_start)
}

pub(super) fn parse<T: AsRef<str>>(script: T) -> Result<Block> {
    let script = script.as_ref();
    parser().parse(script).into_result().map_err(|errors| {
        anyhow!(
            "Script parsing failed:\n{}",
            errors
                .into_iter()
                .map(|e| {
                    let span = e.span();
                    let (start_line, start_char) = get_line_number(script, span.start);
                    let (end_line, end_char) = get_line_number(script, span.end);
                    format!(
                        "{} (line {}:{} to line {}:{})",
                        e.reason(),
                        start_line,
                        start_char,
                        end_line,
                        end_char
                    )
                })
                .join("\n")
        )
    })
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
    fn test_float_multiple_fractional_zeros() {
        let stmt = one_statement("3.00; ");
        match stmt {
            Statement::Expression(Expression::Float(f)) => {
                assert!((f - 3.00).abs() < f32::EPSILON)
            }
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
            panic!("Statement was not a method call");
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
        let Expression::FunctionDefinition(keyword, args, body) = *value else {
            panic!("Value was not a function definition");
        };
        assert_eq!(keyword, FuncKeyword::Full);
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
        let Statement::Expression(Expression::FunctionDefinition(keyword, args, body)) = stmt else {
            panic!("Value was not a function definition");
        };
        assert_eq!(keyword, FuncKeyword::Full);
        assert_eq!(args.len(), 2);
        assert_eq!(args[0].as_str(), "a");
        assert_eq!(args[1].as_str(), "b");
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

    #[test]
    fn test_if_no_semicolon() {
        let parser = parser();
        let result = parser
            .parse(
                "\
?i(#a eq 1) {
} ?i (#a eq 2) {
}
",
            )
            .unwrap();
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_float_zero_fraction_round_trip() {
        let stmt = one_statement("3.0;");
        let formatted = stmt.to_string();
        let stmt2 = one_statement(&formatted);
        assert!(matches!(stmt2, Statement::Expression(Expression::Float(_))));
    }

    #[test]
    fn test_assign() {
        let stmt = one_statement("#a = #b;");
        assert!(matches!(
            stmt,
            Statement::Expression(Expression::MethodCall(_, _, _))
        ));
    }

    #[test]
    fn test_method_chain() {
        let stmt = one_statement("(#a eq #b) and (#c eq 0) and (#d eq 0);");
        let Statement::Expression(Expression::MethodCall(first_call, _, _)) = stmt else {
            panic!("Statement was not a method call expression");
        };
        assert!(matches!(*first_call, Expression::MethodCall(_, _, _)));
    }

    #[test]
    fn test_last_statement_no_semicolon() {
        let stmt = one_statement(
            "
        ?i (#a eq 1) {
            Func1
        };
        ",
        );
        let Statement::Conditional(Conditional(_, block, None), None) = stmt else {
            panic!("Statement was not an if statement with no else or else-if");
        };
        assert_eq!(block.len(), 1);
        assert!(matches!(
            block[0],
            Statement::Expression(Expression::FunctionCall(_, _))
        ));
    }

    #[test]
    fn test_leading_zero() {
        let stmt = one_statement("SetEventID 09;");
        let Statement::Expression(Expression::FunctionCall(ref s, ref args)) = stmt else {
            panic!("Statement was not a function call expression");
        };
        assert_eq!(s, "SetEventID");
        assert_eq!(args.len(), 1);
        assert!(matches!(args[0], Expression::Int(9)));
    }

    #[test]
    fn test_trailing_comma() {
        let stmt = one_statement("SubEventMode 58, 8, 3, 0,;");
        let Statement::Expression(Expression::FunctionCall(ref s, ref args)) = stmt else {
            panic!("Statement was not a function call expression");
        };
        assert_eq!(s, "SubEventMode");
        assert_eq!(args.len(), 4);
        assert!(matches!(
            (&args[0], &args[1], &args[2], &args[3]),
            (
                Expression::Int(58),
                Expression::Int(8),
                Expression::Int(3),
                Expression::Int(0)
            )
        ));
        // the trailing comma is preserved (a comma always renders with a following space)
        assert_eq!(stmt.to_string(), "SubEventMode 58, 8, 3, 0, ;");
    }

    #[test]
    fn test_duplicate_comma() {
        let stmt = one_statement(
            "SetCameraPos 0, -13.19, 3.96, 4.90, -7.39, 6.96, 9.17, , 0.00, 0.00, 0.00001, 0, 10;",
        );
        let Statement::Expression(Expression::FunctionCall(ref s, ref args)) = stmt else {
            panic!("Statement was not a function call expression");
        };
        assert_eq!(s, "SetCameraPos");
        assert_eq!(args.len(), 12);
    }

    #[test]
    fn test_duplicate_comma_round_trip() {
        // the doubled comma between the third and fourth arguments is preserved in the output
        // (integers are used here because float literals are normalized on formatting)
        let script = "SetSomething 1, 2, 3, , 4, 5;";
        assert_eq!(one_statement(script).to_string(), script);
    }

    #[test]
    fn test_leading_comma() {
        // some calls have a comma immediately after the function name
        let stmt = one_statement("SubEventMode, 58, 8;");
        let Statement::Expression(Expression::FunctionCall(ref s, ref args)) = stmt else {
            panic!("Statement was not a function call expression");
        };
        assert_eq!(s, "SubEventMode");
        assert_eq!(args.len(), 2);
        assert_eq!(stmt.to_string(), "SubEventMode, 58, 8;");
    }

    #[test]
    fn test_bare_func_def() {
        let stmt = one_statement(
            "
        #MyFunc | {
            $Print \"my cool function\";
        };
        ",
        );
        let Statement::Expression(Expression::ReferenceDeclaration(var, value)) = stmt else {
            panic!("Statement was not a reference declaration expression");
        };
        assert!(matches!(*var, Expression::Variable(Variable(ref s, None)) if s == "MyFunc"));
        let Expression::FunctionDefinition(keyword, args, body) = *value else {
            panic!("Value was not a function definition");
        };
        assert_eq!(keyword, FuncKeyword::None);
        assert!(args.is_empty());
        assert_eq!(body.len(), 1);
    }

    #[test]
    fn test_bare_func_with_args() {
        let stmt = one_statement(
            "
        #MyFunc | (id0,id1){
            $Print \"my cool function\";
        };
        ",
        );
        let Statement::Expression(Expression::ReferenceDeclaration(var, value)) = stmt else {
            panic!("Statement was not a reference declaration expression");
        };
        assert!(matches!(*var, Expression::Variable(Variable(ref s, None)) if s == "MyFunc"));
        let Expression::FunctionDefinition(keyword, args, body) = *value else {
            panic!("Value was not a function definition");
        };
        assert_eq!(keyword, FuncKeyword::None);
        assert_eq!(args.len(), 2);
        assert_eq!(body.len(), 1);
    }

    #[test]
    fn test_identifier_starting_with_digit() {
        let stmt = one_statement("#2ndret_pliantly : 4;");
        let Statement::Expression(Expression::ValueDeclaration(var, value)) = stmt else {
            panic!("Statement was not a value declaration expression");
        };
        assert!(
            matches!(*var, Expression::Variable(Variable(ref s, None)) if s == "2ndret_pliantly")
        );
        let Expression::Int(num) = *value else {
            panic!("Value was not a number literal");
        };
        assert_eq!(num, 4);
    }

    #[test]
    fn test_parameter_with_sigil() {
        let stmt = one_statement(
            "
        #MyFunc | (id0,#id1){
            $Print \"my cool function\";
        };
        ",
        );
        let Statement::Expression(Expression::ReferenceDeclaration(var, value)) = stmt else {
            panic!("Statement was not a reference declaration expression");
        };
        assert!(matches!(*var, Expression::Variable(Variable(ref s, None)) if s == "MyFunc"));
        let Expression::FunctionDefinition(keyword, args, body) = *value else {
            panic!("Value was not a function definition");
        };
        assert_eq!(keyword, FuncKeyword::None);
        assert_eq!(args.len(), 2);
        // the bare name is preserved for matching, but the formatted form keeps the sigil
        assert_eq!(args[0].as_str(), "id0");
        assert_eq!(args[0].to_string(), "id0");
        assert_eq!(args[1].as_str(), "id1");
        assert_eq!(args[1].to_string(), "#id1");
        assert_eq!(body.len(), 1);
    }

    #[test]
    fn test_numeric_parameter_name() {
        let stmt = one_statement(
            "
        #MyFunc | (0, 1) {
            $Print \"my cool function\";
        };
        ",
        );
        let Statement::Expression(Expression::ReferenceDeclaration(_, value)) = stmt else {
            panic!("Statement was not a reference declaration expression");
        };
        let Expression::FunctionDefinition(_, args, _) = *value else {
            panic!("Value was not a function definition");
        };
        assert_eq!(args.len(), 2);
        assert_eq!(args[0].as_str(), "0");
        assert_eq!(args[1].as_str(), "1");
    }

    #[test]
    fn test_func_keyword_round_trip() {
        // each keyword form is reproduced verbatim by the formatter
        for (input, expected) in [
            ("#F | ?F (a) { Foo; };", "#F | ?F (a) {\n\tFoo;\n}"),
            ("#F | ? (a) { Foo; };", "#F | ? (a) {\n\tFoo;\n}"),
            ("#F | (a) { Foo; };", "#F | (a) {\n\tFoo;\n}"),
            ("#F | { Foo; };", "#F | {\n\tFoo;\n}"),
        ] {
            // the formatted statement carries a trailing semicolon
            assert_eq!(one_statement(input).to_string(), format!("{expected};"));
        }
    }

    #[test]
    fn test_extra_semicolon() {
        let parser = parser();
        let mut result = parser
            .parse(
                "\
        SetFixCamera -1, 0;
        ;
        ",
            )
            .unwrap()
            .into_iter();
        let Some(Statement::Expression(Expression::FunctionCall(ref s, ref args))) = result.next()
        else {
            panic!("Statement was not a function call expression");
        };
        assert_eq!(s, "SetFixCamera");
        assert_eq!(args.len(), 2);
        assert!(matches!(
            (&args[0], &args[1]),
            (Expression::Int(-1), Expression::Int(0))
        ));

        assert!(matches!(result.next(), Some(Statement::Empty)));
    }

    #[test]
    fn test_extra_semicolon_in_block() {
        let stmt = one_statement(
            "\
        ?i( #wp eq 0 ) {
            $SetFixCamera -1, 0;
            ;
        };
        ",
        );
        let Statement::Conditional(Conditional(_, block, None), None) = stmt else {
            panic!("Statement was not an if statement with no else or else-if");
        };
        assert_eq!(block.len(), 2);
    }

    #[test]
    fn test_func_def_with_no_f() {
        let stmt = one_statement(
            "
        #MyFunc | ?{
            $Print \"my cool function\";
        };
        ",
        );
        let Statement::Expression(Expression::ReferenceDeclaration(var, value)) = stmt else {
            panic!("Statement was not a reference declaration expression");
        };
        assert!(matches!(*var, Expression::Variable(Variable(ref s, None)) if s == "MyFunc"));
        let Expression::FunctionDefinition(keyword, args, body) = *value else {
            panic!("Value was not a function definition");
        };
        assert_eq!(keyword, FuncKeyword::Bare);
        assert!(args.is_empty());
        assert_eq!(body.len(), 1);
    }

    #[test]
    fn test_space_after_sigil() {
        let stmt = one_statement("# TalkFlag = 11;");
        let Statement::Expression(Expression::MethodCall(obj, method, args)) = stmt else {
            panic!("Statement was not a method call");
        };
        assert!(matches!(*obj, Expression::Variable(Variable(ref s, None)) if s == "TalkFlag"));
        assert_eq!(method, "=");
        assert_eq!(args.len(), 1);
        let mut it = args.into_iter();
        assert!(matches!(it.next().unwrap(), Expression::Int(11)));
    }

    #[test]
    fn test_while_loop() {
        let parser = parser();
        let mut result = parser
            .parse(
                "\
    ?W{
        (#iii le 84)},{
        $AIDeleteCharacter #iii;
        #iii add 1;
    };
            ",
            )
            .unwrap()
            .into_iter();
        let stmt = result.next().unwrap();
        assert!(matches!(stmt, Statement::WhileLoop(_, _)));
        assert!(matches!(result.next(), None));
    }

    #[test]
    fn test_short_break() {
        let stmt = one_statement("/b;");
        assert!(matches!(stmt, Statement::Break));
    }

    #[test]
    fn test_long_break() {
        let stmt = one_statement("/break;");
        assert!(matches!(stmt, Statement::Break));
    }

    #[test]
    fn test_short_return() {
        let stmt = one_statement("/r;");
        assert!(matches!(stmt, Statement::Return));
    }

    #[test]
    fn test_ternary() {
        let stmt = one_statement("?I (#a eq #b), 1, 0;");
        assert!(matches!(
            stmt,
            Statement::Expression(Expression::TernaryConditional(_, _, _))
        ));
    }

    #[test]
    fn test_global_method_call() {
        let stmt = one_statement("$#NandemoGroupRand=random 10;");
        let Statement::Expression(Expression::Global(value)) = stmt else {
            panic!("Statement was not a global");
        };
        assert!(matches!(*value, Expression::MethodCall(_, _, _)));
    }

    #[test]
    fn test_line_comment() {
        // comments should be skipped like whitespace, wherever they appear
        let stmt = one_statement("// leading comment\n4 // trailing comment\n;");
        assert!(matches!(stmt, Statement::Expression(Expression::Int(4))));
    }

    #[test]
    fn test_comment_only() {
        let parser = parser();
        let result = parser.parse("// just a comment\n").unwrap();
        assert!(result.is_empty());
    }
}
