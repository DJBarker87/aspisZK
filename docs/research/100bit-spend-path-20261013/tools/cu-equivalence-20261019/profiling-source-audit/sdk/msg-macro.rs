macro_rules! msg {
    ($msg:expr) => {
        $crate::sol_log($msg)
    };
    ($($arg:tt)*) => ($crate::sol_log(&format!($($arg)*)));
}