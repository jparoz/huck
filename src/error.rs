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

// @Cleanup: not pub
#[derive(Debug)]
pub struct Location<'a> {
    filename: &'a str,
    start: Position,
    end: Position,
}

impl<'a> Location<'a> {
    // @Cleanup: not pub
    pub fn new(filename: &str) -> Location {
        Location {
            filename: filename,
            start: Position::default(),
            end: Position::default(),
        }
    }
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

// @Cleanup: not pub
#[derive(Debug)]
pub struct Position {
    line: usize,
    column: usize,
}

impl Default for Position {
    fn default() -> Position {
        Position {
            line: 1,
            column: 0,
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

macro_rules! error {
    ($toks:expr, $et:expr, $start:expr, $end:expr, $str:expr) => {
        Error {error_type: $et, location: $toks.get_location($start, $end), message: $str.to_string()}
    };
    ($toks:expr, $et:expr, $start:expr, $end:expr, $str:expr, $($arg:tt)*) => {
        Error {error_type: $et, location: $toks.get_location($start, $end), message: format!($str, $($arg)*)}
    };
}
