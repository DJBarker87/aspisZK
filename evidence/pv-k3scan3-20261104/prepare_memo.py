from pathlib import Path
import re,json
E=Path(__file__).resolve().parent;P=E/'caller';t=(E/'memo.frozen.rs').read_text()
a=t.index('pub fn mul');t=t[a:]
t=t.replace('pub fn mul(a:QM31,b:QM31)->QM31 {eval(0,a,b)}','pub fn mul(a:QM31,b:QM31,log:&mut Memo)->QM31 {eval(0,a,b,log)}').replace('pub fn square(a:QM31)->QM31 {eval(1,a,a)}','pub fn square(a:QM31,log:&mut Memo)->QM31 {eval(1,a,a,log)}').replace('fn eval(tag:u8,a:QM31,b:QM31)->QM31 {unsafe {','fn eval(tag:u8,a:QM31,b:QM31,log:&mut Memo)->QM31 {{').replace('pub fn roundtrip16() {unsafe {','pub fn roundtrip16(log:&mut Memo) {{').replace('super::equivalence16::q()','super::q()').replace('mul(QM31::ONE,QM31::ZERO)','mul(QM31::ONE,QM31::ZERO,log)')
for n in ['USED','TAG','LEFT','RIGHT','OUTPUT']:t=re.sub(r'\b'+n+r'\b','log.'+n.lower(),t)
header='''use aspis_core::field::QM31;
const CAP:usize=64;
pub struct Memo {pub used:usize,pub tag:[u8;CAP],pub left:[QM31;CAP],pub right:[QM31;CAP],pub output:[QM31;CAP]}
impl Memo {pub fn new()->Self {Self{used:0,tag:[0;CAP],left:[QM31::ZERO;CAP],right:[QM31::ZERO;CAP],output:[QM31::ZERO;CAP]}}}
'''
(P/'shared_callee16.rs').write_text(header+t)
with (P/'lib.rs').open('a') as f:f.write('''
mod shared_callee16;
mod equivalence16 {
 use super::*;
 #[kani::proof] #[kani::unwind(128)]
 fn shared_repeat16() {
  let mut log=shared_callee16::Memo::new();
  shared_callee16::roundtrip16(&mut log);
  let a=q();let b=q();
  let x=shared_callee16::mul(a,b,&mut log);
  let y=shared_callee16::mul(a,b,&mut log);
  check(x,y);
  assert_eq!(log.used,1);assert_eq!(log.tag[0],0);
  assert_eq!(log.left[0],a);assert_eq!(log.right[0],b);assert_eq!(log.output[0],x);
 }
}
''')
for i,n in [(91906,False),(91907,True)]:
 (E/f'config-K{i}.json').write_text(json.dumps({'harness':'equivalence16::shared_repeat16','credit':'C156','negative':n},indent=2)+'\n')
