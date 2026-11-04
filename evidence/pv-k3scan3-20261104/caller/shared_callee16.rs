use aspis_core::field::QM31;
const CAP:usize=64;
pub struct Memo {pub used:usize,pub tag:[u8;CAP],pub left:[QM31;CAP],pub right:[QM31;CAP],pub output:[QM31;CAP]}
impl Memo {pub fn new()->Self {Self{used:0,tag:[0;CAP],left:[QM31::ZERO;CAP],right:[QM31::ZERO;CAP],output:[QM31::ZERO;CAP]}}}
pub fn mul(a:QM31,b:QM31,log:&mut Memo)->QM31 {eval(0,a,b,log)}
pub fn square(a:QM31,log:&mut Memo)->QM31 {eval(1,a,a,log)}
fn eval(tag:u8,a:QM31,b:QM31,log:&mut Memo)->QM31 {{
 let mut i=0;while i<log.used {if log.tag[i]==tag && log.left[i]==a && log.right[i]==b {return log.output[i];}i+=1;}
 assert!(log.used<CAP,"shared function table capacity");let r=super::q();
 log.tag[log.used]=tag;log.left[log.used]=a;log.right[log.used]=b;log.output[log.used]=r;log.used+=1;r
}}
/// Detect loss of any limb through the exact table key/output copy shape.
pub fn roundtrip16(log:&mut Memo) {{let raw:[u32;4]=kani::any();let a=QM31{c0:aspis_core::field::CM31{a:aspis_core::field::M31(raw[0]),b:aspis_core::field::M31(raw[1])},c1:aspis_core::field::CM31{a:aspis_core::field::M31(raw[2]),b:aspis_core::field::M31(raw[3])}};
 log.used=1;log.tag[0]=0;log.left[0]=QM31::ONE;log.right[0]=QM31::ZERO;log.output[0]=a;
 let r=mul(QM31::ONE,QM31::ZERO,log);let words=[r.c0.a.0,r.c0.b.0,r.c1.a.0,r.c1.b.0];let k:usize=kani::any();kani::assume(k<4);assert_eq!(words[k],raw[k]);log.used=0;
}}
