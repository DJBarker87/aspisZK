pub fn option_ok_or<T,E>(value:Option<T>,error:E)->Result<T,E>{value.ok_or(error)}
pub fn option_eq<T:PartialEq>(a:&Option<T>,b:&Option<T>)->bool{a.eq(b)}
