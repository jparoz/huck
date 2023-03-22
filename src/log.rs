// @Todo @Cleanup: These should be more systematically named
#[allow(dead_code)]
#[rustfmt::skip] pub const DEBUG     : &str = "     debug";
#[rustfmt::skip] pub const METRICS   : &str = "   metrics";
#[rustfmt::skip] pub const FILE      : &str = "      file";
#[rustfmt::skip] pub const IMPORT    : &str = "    import";
#[rustfmt::skip] pub const PARSE     : &str = "     parse";
#[rustfmt::skip] pub const RESOLVE   : &str = "   resolve";
#[rustfmt::skip] pub const TYPECHECK : &str = " typecheck";
#[rustfmt::skip] pub const CODEGEN   : &str = "   codegen";

#[allow(unused_macros)]
#[macro_export]
macro_rules! error {
    ($target:expr, $($arg:tt)+) => (log_crate::log!(target: $target, log_crate::Level::Error, $($arg)+))
}
#[allow(unused_imports)]
pub use error;

#[allow(unused_macros)]
#[macro_export]
macro_rules! log_warn {
    ($target:expr, $($arg:tt)+) => (log_crate::log!(target: $target, log_crate::Level::Warn, $($arg)+))
}
#[allow(unused_imports)]
pub use log_warn as warn;

#[allow(unused_macros)]
#[macro_export]
macro_rules! info {
    ($target:expr, $($arg:tt)+) => (log_crate::log!(target: $target, log_crate::Level::Info, $($arg)+))
}
#[allow(unused_imports)]
pub use info;

#[allow(unused_macros)]
#[macro_export]
macro_rules! trace {
    ($target:expr, $($arg:tt)+) => (log_crate::log!(target: $target, log_crate::Level::Trace, $($arg)+))
}
#[allow(unused_imports)]
pub use trace;

/// Debug is different
#[allow(unused_macros)]
#[macro_export]
macro_rules! debug {
    ($lit:literal, $($arg:tt)+) => (log_crate::log!(
            target: $crate::log::DEBUG,
            log_crate::Level::Debug,
            $lit, $($arg)+)
        );
    ($lit:literal) => (log_crate::log!(
            target: $crate::log::DEBUG,
            log_crate::Level::Debug,
            $lit)
        );
    ($arg:expr) => (log_crate::log!(
            target: $crate::log::DEBUG,
            log_crate::Level::Debug,
            concat!(stringify!($arg), ": {:?}"), $arg)
        );
}
#[allow(unused_imports)]
pub use debug;
