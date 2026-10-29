use std::fmt::{self,Write};
struct Reject{calls:usize}
impl Write for Reject {fn write_str(&mut self,_s:&str)->fmt::Result{self.calls+=1;Err(fmt::Error)}}
fn main(){
 assert!(!cfg!(debug_assertions));let negative=std::env::args().any(|s|s=="--negative");
 let mut reject=Reject{calls:0};let rejected=fmt::write(&mut reject,format_args!("{}",17usize));
 assert!(reject.calls>0);assert_eq!(rejected.is_err(),!negative,"the source formatter propagates the writer Err");
 let mut accept=String::new();let accepted=fmt::write(&mut accept,format_args!("{}",17usize));assert!(accepted.is_ok());assert_eq!(accept,"17");
 println!("usize_Display_fmt: rejecting writer returns Err; accepting writer returns Ok and writes 17; candidate no-op always-Ok model is not a universal source law");
}
