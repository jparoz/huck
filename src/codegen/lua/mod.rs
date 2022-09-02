use crate::ast::Assignment;
use crate::scope::Scope;

pub trait Generate {
    fn generate(&self) -> String;
}

impl<'file> Generate for Scope<'file> {
    /// Generate Lua code for the given Scope.
    /// This will generate a Lua chunk which returns a table containing the definitions given in the
    /// Huck scope.
    fn generate(&self) -> String {
        let mut lua = "return {".to_string();

        // lua.push_str("")
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

impl<'file> Generate for Assignment<'file> {
    fn generate(&self) -> String {
        let lua = String::new();
        let (lhs, expr) = self;
        todo!()
    }
}
