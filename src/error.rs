use std::fmt;

#[derive(Debug)]
pub struct Error<'a> {
    // @Cleanup: not pub
    pub error_type: ErrorType,
    pub message: String,
    pub location: Location<'a>,
}

#[derive(Debug)]
pub enum ErrorType {
    Lex,
    Parse,
}

// @Cleanup: not pub (??)
#[derive(Debug)]
pub struct Location<'a> {
    pub filename: &'a str,
    pub start: Position,
    pub end: Position,
}

impl<'a> fmt::Display for Location<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:", self.filename)?;

        if self.start.line == self.end.line {
            write!(f, "{}:", self.start.line)?;
        } else {
            write!(f, "{}-{}:", self.start.line, self.end.line)?;
        }

        if self.start.column == self.end.column {
            write!(f, "{}", self.start.column)?;
        } else {
            write!(f, "{}-{}", self.start.column, self.end.column)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Position {
    pub line: usize,
    pub column: usize,
}

impl Default for Position {
    fn default() -> Position {
        Position {
            line: 1,
            column: 1,
        }
    }
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,
               "{:?} error at {}: {}",
               self.error_type,
               self.location,
               self.message)
    }
}
