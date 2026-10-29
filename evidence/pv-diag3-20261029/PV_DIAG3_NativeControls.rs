use std::io::{self,Write};
use std::sync::{Arc,Mutex};
use std::collections::VecDeque;
use std::fmt;
#[derive(Debug)]
struct Notice(Arc<Mutex<Vec<String>>>, &'static str);
impl fmt::Display for Notice { fn fmt(&self,f:&mut fmt::Formatter<'_>)->fmt::Result{f.write_str(self.1)} }
impl std::error::Error for Notice {}
impl Drop for Notice { fn drop(&mut self){self.0.lock().unwrap().push(format!("drop:{}",self.1));} }
struct Script { steps:VecDeque<i32>, delivered:Vec<u8>, log:Arc<Mutex<Vec<String>>> }
impl Write for Script {
 fn write(&mut self,b:&[u8])->io::Result<usize>{
  self.log.lock().unwrap().push(format!("write:{}",b.len()));
  let n=self.steps.pop_front().unwrap_or(b.len() as i32);
  match n {
   -1=>Err(io::Error::new(io::ErrorKind::Interrupted,Notice(self.log.clone(),"interrupted"))),
   -2=>Err(io::Error::new(io::ErrorKind::Other,Notice(self.log.clone(),"failed"))),
   n=>{let k=(n as usize).min(b.len());self.delivered.extend_from_slice(&b[..k]);Ok(k)}
  }
 }
 fn flush(&mut self)->io::Result<()>{Ok(())}
}
struct BadFmt;
impl fmt::Display for BadFmt {fn fmt(&self,_:&mut fmt::Formatter<'_>)->fmt::Result{Err(fmt::Error)}}
fn main(){
 let log=Arc::new(Mutex::new(Vec::new()));
 let mut a=Script{steps:VecDeque::from(vec![2,-1,1,9]),delivered:vec![],log:log.clone()};
 a.write_all(b"abcdef").unwrap();assert_eq!(a.delivered,b"abcdef");
 assert_eq!(*log.lock().unwrap(),vec!["write:6","write:4","drop:interrupted","write:4","write:3"]);
 log.lock().unwrap().clear();
 let mut b=Script{steps:VecDeque::from(vec![2,0]),delivered:vec![],log:log.clone()};
 assert_eq!(b.write_all(b"abcdef").unwrap_err().kind(),io::ErrorKind::WriteZero);assert_eq!(b.delivered,b"ab");
 log.lock().unwrap().clear();
 let mut c=Script{steps:VecDeque::from(vec![1,-2]),delivered:vec![],log:log.clone()};
 let e=c.write_all(b"abcdef").unwrap_err();assert_eq!(c.delivered,b"a");
 assert_eq!(*log.lock().unwrap(),vec!["write:6","write:5"]);drop(e);
 assert_eq!(*log.lock().unwrap(),vec!["write:6","write:5","drop:failed"]);
 log.lock().unwrap().clear();
 let mut d=Script{steps:VecDeque::from(vec![-2]),delivered:vec![],log:log.clone()};
 let e=d.write_fmt(format_args!("{}",7)).unwrap_err();assert_eq!(e.kind(),io::ErrorKind::Other);drop(e);
 assert_eq!(*log.lock().unwrap(),vec!["write:1","drop:failed"]);
 let old=std::panic::take_hook();std::panic::set_hook(Box::new(|_|{}));
 let mut e=Script{steps:VecDeque::new(),delivered:vec![],log:log.clone()};
 assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||e.write_fmt(format_args!("{}",BadFmt)))).is_err());
 log.lock().unwrap().clear();
 assert!(std::panic::catch_unwind({let log=log.clone(); move ||{let _a=Notice(log.clone(),"outer");let _b=Notice(log.clone(),"inner");panic!("control");}}).is_err());
 assert_eq!(*log.lock().unwrap(),vec!["drop:inner","drop:outer"]);
 std::panic::set_hook(old);
 log.lock().unwrap().clear();
 let x=anyhow::Error::new(Notice(log.clone(),"anyhow"));drop(x);assert_eq!(*log.lock().unwrap(),vec!["drop:anyhow"]);
 assert_eq!(std::backtrace::Backtrace::disabled().status(),std::backtrace::BacktraceStatus::Disabled);
 assert_eq!(std::backtrace::Backtrace::capture().status(),std::backtrace::BacktraceStatus::Disabled);
 let capture=std::backtrace::Backtrace::force_capture();assert_eq!(capture.status(),std::backtrace::BacktraceStatus::Captured);drop(capture);
 println!("PASS partial, interrupted-drop, zero, retained-error, adapter-error, spurious-fmt-panic, unwind-order, anyhow-drop, backtrace-status");
}
