// A safe reference for the frozen read-only indexed scalar/record helpers.
pub fn cell<T>(values:&[T],index:usize)->&T {&values[index]}
