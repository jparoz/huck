#[rustfmt::skip] pub const METRICS   : &str = "   metrics";
#[rustfmt::skip] pub const IMPORT    : &str = "    import";
#[rustfmt::skip] pub const PARSE     : &str = "     parse";
#[rustfmt::skip] pub const TYPECHECK : &str = " typecheck";
#[rustfmt::skip] pub const CODEGEN   : &str = "   codegen";

#[allow(unused_macros)]
macro_rules! error {
    ($target:expr, $($arg:tt)+) => (log_crate::log!(target: $target, log_crate::Level::Error, $($arg)+))
}
#[allow(unused_imports)]
pub(crate) use error;

#[allow(unused_macros)]
macro_rules! log_warn {
    ($target:expr, $($arg:tt)+) => (log_crate::log!(target: $target, log_crate::Level::Warn, $($arg)+))
}
#[allow(unused_imports)]
pub(crate) use log_warn as warn;

#[allow(unused_macros)]
macro_rules! info {
    ($target:expr, $($arg:tt)+) => (log_crate::log!(target: $target, log_crate::Level::Info, $($arg)+))
}
#[allow(unused_imports)]
pub(crate) use info;

#[allow(unused_macros)]
macro_rules! debug {
    ($target:expr, $($arg:tt)+) => (log_crate::log!(target: $target, log_crate::Level::Debug, $($arg)+))
}
#[allow(unused_imports)]
pub(crate) use debug;

#[allow(unused_macros)]
macro_rules! trace {
    ($target:expr, $($arg:tt)+) => (log_crate::log!(target: $target, log_crate::Level::Trace, $($arg)+))
}
#[allow(unused_imports)]
pub(crate) use trace;
