use super::super::{E,QM31 as K};
// Receipt-only source. The active version is a cfg(kani) scratch addition.
const NEV_DOT_B:u64=4611686009837453316;
struct NEV_DotCellLog { left:u64,right:u64,reply:u64,calls:u8 }
impl NEV_DotCellLog { fn call(&mut self,left:u64,right:u64)->u64 {self.left=left;self.right=right;self.calls+=1;self.reply} }
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn dots_term_cell() {
 let mut sums:[u64;8]=kani::any();let lane:usize=kani::any();let observed:usize=kani::any();kani::assume(lane<8 && observed<8);
 let old=sums[observed];let selected=sums[lane];kani::assume(selected<=13835058029512359948u64);
 let coefficient:u32=kani::any();let scalar:u32=kani::any();kani::assume(coefficient<2147483647 && scalar<2147483647);
 let reply:u64=kani::any();kani::assume(reply<=NEV_DOT_B);
 let mut log=NEV_DotCellLog{left:0,right:0,reply,calls:0};
 let product=log.call(u64::from(coefficient),u64::from(scalar));sums[lane]+=product;
 assert_eq!(log.calls,1);assert_eq!(log.left,u64::from(coefficient));assert_eq!(log.right,u64::from(scalar));
 let expected=if observed==lane{old+reply}else{old};
 assert_eq!(sums[observed],if cfg!(NEV_wrong_dots_term){expected^1}else{expected});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn dots_fold_cell() {
 let mut limbs:[u64;8]=kani::any();let sums:[u64;8]=kani::any();let lane:usize=kani::any();let observed:usize=kani::any();kani::assume(lane<8 && observed<8);
 kani::assume(limbs[lane]<137438953472u64);let old=limbs[observed];let selected=sums[lane];
 limbs[lane]+=(sums[lane]&0x7fff_ffff)+(sums[lane]>>31);
 let folded=(selected&0x7fff_ffff)+(selected>>31);assert!(folded<17179869184u64);
 let expected=if observed==lane{old+folded}else{old};assert_eq!(limbs[observed],if cfg!(NEV_wrong_dots_fold){expected^1}else{expected});
}
#[kani::proof] #[kani::unwind(80)]
fn dots_outer_cursor() {
 let batch:usize=kani::any();kani::assume(batch<7);let start=batch*4;
 // Source-reachable arbitrary pre-state: first flag or one preceding yield.
 // StepBy stores Range.start and first_take only (pinned std source review).
 let mut source=(if batch==0{0}else{start-4}..26).step_by(4);
 if batch>0 {assert_eq!(source.next(),Some(start-4));}
 let got=source.next();assert_eq!(got,Some(if cfg!(NEV_wrong_dots_cursor){start+1}else{start}));
 let end=core::cmp::min(start+4,26);assert!(start<end && end<=26 && end-start<=4);
 let term:usize=kani::any();kani::assume(term>=start && term<end);let mut inner=term..end;
 assert_eq!(inner.next(),Some(term));assert_eq!(inner.start,term+1);assert_eq!(inner.end,end);
}
fn NEV_dots_wide()->E {let words:[u32;8]=kani::any();for word in words {kani::assume(word<2147483647);} E::from_limbs(words).unwrap()}
struct NEV_FourLog { qptr:[usize;4],gptr:[usize;4],slot:[usize;4],calls:usize,reply:[E;4] }
impl NEV_FourLog {
 fn call(&mut self,q:&[u8;608],g:&[E;29],slot:usize)->E {
  let at=self.calls;self.qptr[at]=q.as_ptr() as usize;self.gptr[at]=g.as_ptr() as usize;self.slot[at]=slot;self.calls+=1;self.reply[slot]
 }
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn dots_wrapper_context() {
 let bytes:[u8;609]=kani::any();let long:bool=kani::any();let length=if long{609}else{608};let q=&bytes[..length];
 let g:[E;29]=core::array::from_fn(|_|NEV_dots_wide());let reply:[E;4]=core::array::from_fn(|_|NEV_dots_wide());
 let mut log=NEV_FourLog{qptr:[0;4],gptr:[0;4],slot:[99;4],calls:0,reply};
 let input:&[u8;608]=q[..608].try_into().unwrap();
 let out=[log.call(input,&g,0),log.call(input,&g,1),log.call(input,&g,2),log.call(input,&g,3)];
 let observed:usize=kani::any();kani::assume(observed<4);assert_eq!(log.calls,4);
 assert_eq!(log.qptr[observed],q.as_ptr() as usize);assert_eq!(log.gptr[observed],g.as_ptr() as usize);assert_eq!(log.slot[observed],observed);
 let lane:usize=kani::any();kani::assume(lane<8);let expected=reply[observed].to_limbs()[lane];
 assert_eq!(out[observed].to_limbs()[lane],if cfg!(NEV_wrong_dots_wrapper){expected^1}else{expected});
}
struct NEV_TailContextLog { calls:usize,receiver:[usize;3],value:[[u32;8];3],scalar:[[u32;4];3],old:[[u64;8];3],sums:[[u64;8];3],finish:[u64;8],addleft:[u32;8],addright:[u32;8],finished:E,added:E }
fn NEV_qwords(x:K)->[u32;4] {[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
impl NEV_TailContextLog {
 fn push(&mut self,receiver:&mut EbyKDot,value:E,scalar:K) {
  let at=self.calls;assert_eq!(receiver.count,at);assert!(at<3);self.receiver[at]=receiver as *mut EbyKDot as usize;
  self.value[at]=value.to_limbs();self.scalar[at]=NEV_qwords(scalar);self.old[at]=[receiver.c0.sums[0],receiver.c0.sums[1],receiver.c0.sums[2],receiver.c0.sums[3],receiver.c1.sums[0],receiver.c1.sums[1],receiver.c1.sums[2],receiver.c1.sums[3]];
  receiver.c0.sums=[self.sums[at][0],self.sums[at][1],self.sums[at][2],self.sums[at][3]];receiver.c1.sums=[self.sums[at][4],self.sums[at][5],self.sums[at][6],self.sums[at][7]];receiver.count+=1;self.calls+=1;
 }
 fn finish(&mut self,value:EbyKDot)->E {assert_eq!(value.count,3);self.finish=[value.c0.sums[0],value.c0.sums[1],value.c0.sums[2],value.c0.sums[3],value.c1.sums[0],value.c1.sums[1],value.c1.sums[2],value.c1.sums[3]];self.calls+=1;self.finished}
 fn add(&mut self,left:E,right:E)->E {assert_eq!(self.calls,4);self.addleft=left.to_limbs();self.addright=right.to_limbs();self.calls+=1;self.added}
}
fn NEV_dots_tail(q:&[u8;608],g:&[E;29],slot:usize,value:E,log:&mut NEV_TailContextLog)->Result<E,()> {
 let mut tail=EbyKDot::new();
 let scalar=K::from_le_bytes(&q[slot*120+104..slot*120+120]).ok_or(())?;log.push(&mut tail,g[28],scalar);
 let offset0=480+slot*32+0*16;let scalar=K::from_le_bytes(&q[offset0..offset0+16]).ok_or(())?;log.push(&mut tail,g[0+26],scalar);
 let offset1=480+slot*32+1*16;let scalar=K::from_le_bytes(&q[offset1..offset1+16]).ok_or(())?;log.push(&mut tail,g[1+26],scalar);
 let finished=log.finish(tail);Ok(log.add(value,finished))
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn dots_tail_context() {
 let q:[u8;608]=kani::any();let g:[E;29]=core::array::from_fn(|_|NEV_dots_wide());let slot:usize=kani::any();kani::assume(slot<4);let value=NEV_dots_wide();
 let mut log=NEV_TailContextLog{calls:0,receiver:[0;3],value:[[0;8];3],scalar:[[0;4];3],old:[[0;8];3],sums:kani::any(),finish:[0;8],addleft:[0;8],addright:[0;8],finished:NEV_dots_wide(),added:NEV_dots_wide()};
 let out=NEV_dots_tail(&q,&g,slot,value,&mut log);assert!(log.calls<=5);
 let observed:usize=kani::any();kani::assume(observed<3);
 if log.calls>observed {
  let which=if observed==0{28}else{25+observed};assert_eq!(log.value[observed],g[which].to_limbs());
  let start=if observed==0{slot*120+104}else{480+slot*32+(observed-1)*16};
  let expected=K::from_le_bytes(&q[start..start+16]).unwrap();assert_eq!(log.scalar[observed],NEV_qwords(expected));
  if observed>0{assert_eq!(log.receiver[observed],log.receiver[0]);assert_eq!(log.old[observed],log.sums[observed-1]);}else{assert_eq!(log.old[0],[0;8]);}
 }
 if let Ok(actual)=out {assert_eq!(log.calls,5);assert_eq!(log.finish,log.sums[2]);assert_eq!(log.addleft,value.to_limbs());assert_eq!(log.addright,log.finished.to_limbs());assert_eq!(actual.to_limbs(),log.added.to_limbs());}
 assert_eq!(out.is_ok(),if cfg!(NEV_wrong_dots_tail){log.calls!=5}else{log.calls==5});
}
struct NEV_TailParserLog { pointer:usize,length:usize,reply:Option<K>,calls:usize }
impl NEV_TailParserLog {fn call(&mut self,window:&[u8])->Option<K>{self.pointer=window.as_ptr() as usize;self.length=window.len();self.calls+=1;self.reply}}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn dots_tail_window() {
 let q:[u8;608]=kani::any();let slot:usize=kani::any();let position:usize=kani::any();kani::assume(slot<4 && position<3);
 let coefficient=NEV_dots_wide();let left:[u64;4]=kani::any();let right:[u64;4]=kani::any();
 let mut receiver=EbyKDot{c0:Dot{sums:left},c1:Dot{sums:right},count:position};let pointer=&mut receiver as *mut EbyKDot as usize;
 let word:[u32;4]=kani::any();for v in word{kani::assume(v<P);}let scalar=K{c0:aspis_core::field::CM31{a:aspis_core::field::M31(word[0]),b:aspis_core::field::M31(word[1])},c1:aspis_core::field::CM31{a:aspis_core::field::M31(word[2]),b:aspis_core::field::M31(word[3])}};
 let exists:bool=kani::any();let mut parser=NEV_TailParserLog{pointer:0,length:0,reply:if exists{Some(scalar)}else{None},calls:0};
 let prefix=NEV_dots_wide();let mut log=NEV_TailContextLog{calls:position,receiver:[0;3],value:[[0;8];3],scalar:[[0;4];3],old:[[0;8];3],sums:kani::any(),finish:[0;8],addleft:[0;8],addright:[0;8],finished:NEV_dots_wide(),added:NEV_dots_wide()};
 let start=if position==0{slot*120+104}else{480+slot*32+(position-1)*16};
 let got=parser.call(&q[start..start+16]);assert_eq!(parser.calls,1);assert_eq!(parser.pointer,q.as_ptr() as usize+start);assert_eq!(parser.length,16);
 if let Some(decoded)=got {
  let which=if position==0{28}else{25+position};assert!(which>=26 && which<=28);log.push(&mut receiver,coefficient,decoded);
  assert_eq!(log.calls,position+1);assert_eq!(receiver.count,position+1);assert_eq!(log.receiver[position],pointer);
  assert_eq!(log.old[position],[left[0],left[1],left[2],left[3],right[0],right[1],right[2],right[3]]);
  assert_eq!(log.scalar[position],word);assert_eq!(log.value[position],coefficient.to_limbs());
  let lane:usize=kani::any();kani::assume(lane<4);assert_eq!(receiver.c0.sums[lane],log.sums[position][lane]);assert_eq!(receiver.c1.sums[lane],log.sums[position][lane+4]);
  if position==2 {let finished=log.finish(receiver);let out=log.add(prefix,finished);assert_eq!(log.finish,log.sums[2]);assert_eq!(log.addleft,prefix.to_limbs());assert_eq!(log.addright,log.finished.to_limbs());assert_eq!(out.to_limbs(),log.added.to_limbs());assert_eq!(log.calls,5);}
 }else{assert_eq!(log.calls,position);assert_eq!(receiver.count,position);assert_eq!(receiver.c0.sums,left);assert_eq!(receiver.c1.sums,right);}
 assert_eq!(exists,if cfg!(NEV_wrong_dots_tail_window){got.is_none()}else{got.is_some()});
}
