use std::fmt::{self,Write};
struct Reject{calls:usize,seen:String}
impl Write for Reject {
 fn write_str(&mut self,s:&str)->fmt::Result{
  if s.is_empty(){return Ok(());}
  self.calls+=1;self.seen.push_str(s);Err(fmt::Error)
 }
}
fn checked_write(output:&mut dyn Write,args:fmt::Arguments<'_>)->fmt::Result{
 assert!(args.as_str().is_none(),"must enter the argument-formatting path, not the literal-string shortcut");
 fmt::write(output,args)
}
fn main(){
 assert!(!cfg!(debug_assertions));let negative=std::env::args().any(|s|s=="--negative");
 let value:usize=std::hint::black_box(17usize);
 let mut reject=Reject{calls:0,seen:String::new()};
 let rejected=checked_write(&mut reject,format_args!("{}",value));
 assert_eq!(reject.calls,1);assert_eq!(reject.seen,"17");
 assert_eq!(rejected.is_err(),!negative,"numeric Display propagates the writer Err");
 let mut accept=String::new();let accepted=checked_write(&mut accept,format_args!("{}",value));
 assert!(accepted.is_ok());assert_eq!(accept,"17");
 println!("usize_Display_fmt: Arguments::as_str=None; numeric payload=17; rejecting writer returns Err; accepting writer returns Ok; always-Ok model refuted at this source instance");
}
