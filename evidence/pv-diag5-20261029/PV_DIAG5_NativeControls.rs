use std::backtrace::{Backtrace,BacktraceStatus};
use std::fmt::{self,Write};
struct StopFmt { calls: usize }
impl Write for StopFmt {
 fn write_str(&mut self,_: &str)->fmt::Result {self.calls+=1;Err(fmt::Error)}
}
fn collect(ip:usize, symbols:&[usize])->(Vec<usize>,Option<usize>){
 let mut frames=Vec::new();let mut actual_start=None;
 for &symbol in symbols {
  frames.push(symbol);
  if symbol==ip && actual_start.is_none(){actual_start=Some(frames.len());}
 }
 (frames,actual_start)
}
fn main(){
 let mut checked=0;
 for n in 0..=8 {
  for bits in 0..(1usize<<n) {
   let symbols:Vec<_>=(0..n).map(|i|(bits>>i)&1).collect();
   for ip in 0..3 {
    let (frames,start)=collect(ip,&symbols);
    assert_eq!(frames,symbols);
    assert_eq!(start,symbols.iter().position(|&v|v==ip).map(|i|i+1));
    let k=start.unwrap_or(0);assert!(k<=frames.len());
    assert_eq!(frames[k..].len(),frames.len()-k);checked+=1;
   }
  }
 }
 let disabled=Backtrace::disabled();assert_eq!(disabled.status(),BacktraceStatus::Disabled);
 assert_eq!(format!("{disabled}"),"disabled backtrace");
 assert_eq!(format!("{disabled:#}"),"disabled backtrace");
 let mut out=StopFmt{calls:0};assert!(write!(&mut out,"{disabled}").is_err());assert_eq!(out.calls,1);
 let forced=Backtrace::force_capture();
 let status=forced.status();
 assert!(matches!(status,BacktraceStatus::Captured|BacktraceStatus::Unsupported));
 let short=format!("{forced}");let full=format!("{forced:#}");
 assert!(!short.is_empty()&&!full.is_empty());
 let mut out=StopFmt{calls:0};assert!(write!(&mut out,"{forced}").is_err());assert!(out.calls>=1);
 println!("finite reference callback checks={checked}; disabled literal/formatter-error controls passed; forced status={status:?}; short/full nonempty; source and machine preservation not established");
}
