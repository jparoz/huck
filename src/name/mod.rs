use std::fmt::{self, Display};
use std::sync::atomic::{self, AtomicUsize};

use crate::ast;

mod resolve;
pub use resolve::Resolver;

mod error;
pub use error::Error;

#[cfg(test)]
mod test;

/// A ModulePath is a path to a Huck module, as defined within that module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ModulePath(pub &'static str);

impl Display for ModulePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// An `Ident` is the unqualified part of a name.
pub type Ident = &'static str;

/// An `UnresolvedName` is a Huck identifier
/// which may or may not exist,
/// and which may or may not shadow other identifiers with the same name.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub enum UnresolvedName {
    Unqualified(Ident),
    Qualified(ModulePath, Ident),
}

impl UnresolvedName {
    /// If it's an `Unqualified` name, returns the inner `&'static str`.
    /// If it's a `Qualified` name, returns only the `ident` part (not the path!)
    pub fn ident(&self) -> Ident {
        match self {
            UnresolvedName::Qualified(_, s) | UnresolvedName::Unqualified(s) => s,
        }
    }
}

impl Display for UnresolvedName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnresolvedName::Unqualified(s) => write!(f, "{s}"),
            UnresolvedName::Qualified(path, s) => write!(f, "{path}.{s}"),
        }
    }
}

/// A `ResolvedName` is a unique token, used in the compiler to uniquely identify a value.
/// After name resolution:
/// all names have been confirmed to exist,
/// and all references to a function have the same `ResolvedName`,
/// no matter where the references appear.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct ResolvedName {
    pub source: Source,
    pub ident: Ident,
}

impl ResolvedName {
    pub fn local(ident: Ident) -> Self {
        static UNIQUE_COUNTER: AtomicUsize = AtomicUsize::new(0);
        let id = UNIQUE_COUNTER.fetch_add(1, atomic::Ordering::Relaxed);
        ResolvedName {
            source: Source::Local(id),
            ident,
        }
    }

    pub fn module(path: ModulePath, ident: Ident) -> Self {
        ResolvedName {
            source: Source::Module(path),
            ident,
        }
    }

    pub fn foreign(require: &'static str, foreign_name: ast::ForeignName, ident: Ident) -> Self {
        ResolvedName {
            source: Source::Foreign {
                require,
                foreign_name,
            },
            ident,
        }
    }

    pub fn builtin(ident: Ident) -> Self {
        ResolvedName {
            source: Source::Builtin,
            ident,
        }
    }

    pub fn is_local(&self) -> bool {
        matches!(self.source, Source::Local(..))
    }

    pub fn is_builtin(&self) -> bool {
        matches!(self.source, Source::Builtin)
    }
}

impl Display for ResolvedName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}", self.source, self.ident)
    }
}

/// A `Source` describes where to find an identifier,
/// whether it's a Huck or foreign import,
/// or a local variable (let-binding, etc.).
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Source {
    /// From a Huck module.
    Module(ModulePath),

    /// From a foreign (Lua) module.
    Foreign {
        /// Includes the quotation marks.
        require: &'static str,
        foreign_name: ast::ForeignName,
    },

    /// From e.g. a let binding.
    /// Contains a unique ID,
    /// so that we can tell apart identically-named but different `ResolvedName`s.
    Local(usize),

    /// Compiler builtin
    Builtin,
}

impl Display for Source {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Source::Module(path) => path.fmt(f),
            Source::Foreign {
                require,
                foreign_name,
            } => write!(f, r#"require({require})["{foreign_name}"]"#),
            Source::Local(id) => write!(f, "<local {id}>"),
            Source::Builtin => write!(f, "<compiler builtin>"),
        }
    }
}
