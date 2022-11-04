use crate::ast;
use crate::scope::Scope;

const HUCK_TABLE_NAME: &str = "Huck";

pub trait Generate {
    fn generate(&self) -> String;
}

impl<'file> Generate for Scope<'file> {
    /// Generate Lua code for the given Scope.
    /// This will generate a Lua chunk which returns a table containing the definitions given in the
    /// Huck scope.
    fn generate(&self) -> String {
        let mut lua = "return {".to_string();

        for (name, defn) in self.iter() {
            lua.push_str(&format!("[\"{}\"] = ", name));

            if defn.assignments.len() == 1 {
                // No need for a switch
                lua.push_str(&defn.assignments[0].generate());
            } else {
                // Need to switch on the assignment LHSs using an if-then-elseif-else
                todo!();
            }

            lua.push(',');
        }

        lua.push('}');

        lua
    }
}

impl<'file> Generate for Vec<ast::Assignment<'file>> {
    fn generate(&self) -> String {
        todo!()
    }
}

impl<'file> Generate for ast::Assignment<'file> {
    fn generate(&self) -> String {
        let mut lua = String::new();

        let (lhs, expr) = self;

        match lhs {
            ast::Lhs::Func { name, args } if args.is_empty() => {
                // It's a value
                lua.push_str(&expr.generate());
            }
            ast::Lhs::Func { name, args } => {
                // It's a function
                todo!()
            }
            ast::Lhs::Binop { a, op, b } => {
                // It's a function
                todo!()
            }
        }

        lua
    }
}

impl<'file> Generate for ast::Expr<'file> {
    fn generate(&self) -> String {
        match self {
            ast::Expr::Term(term) => term.generate(),
            ast::Expr::App { func, argument } => {
                let mut lua = String::new();

                // Func (as an expr, surrounded in brackets)
                lua.push('('); // @Note: not strictly necessary?
                lua.push_str(&func.generate());
                lua.push(')'); // @Note: not strictly necessary?

                // Argument (function call syntax)
                // @Note: this assumes functions are curried (? maybe not if tuples desugar to
                // bare (func)(a, b) instead of (func)((a, b)) which doesn't make sense anyway)
                lua.push('(');
                lua.push_str(&argument.generate());
                lua.push(')');

                lua
            }
            ast::Expr::Binop { operator, lhs, rhs } => {
                let mut lua = String::new();

                // @Note @Fixme: this should check for Lua's builtin operators and use those
                // if available

                // Op
                lua.push_str(&format!("{}[\"{}\"]", HUCK_TABLE_NAME, operator));

                // Argument (function call syntax)
                // @Note: this assumes functions are curried (? maybe not if tuples desugar to
                // bare (func)(a, b) instead of (func)((a, b)) which doesn't make sense anyway)
                lua.push('(');
                lua.push_str(&lhs.generate());
                lua.push_str(", ");
                lua.push_str(&rhs.generate());
                lua.push(')');

                lua
            }
            ast::Expr::Let {
                assignments,
                in_expr,
            } => {
                let mut lua = String::new();

                // Open a new function, and local variable declaration
                lua.push_str("(function()\n");

                // Make a new local variable for each assignment
                for assign in assignments.values() {
                    lua.push_str("local ");
                    lua.push_str(&assign.generate()); // @XXX @Fixme: This is certainly wrong
                    lua.push('\n');
                }

                // Generate the in_expr
                lua.push_str("return ");
                lua.push_str(&in_expr.generate());
                lua.push('\n');

                lua.push_str("end)()");

                lua
            }
            ast::Expr::Lambda { args, rhs } => {
                todo!();
            }
        }
    }
}

impl<'file> Generate for ast::Term<'file> {
    fn generate(&self) -> String {
        todo!()
    }
}
