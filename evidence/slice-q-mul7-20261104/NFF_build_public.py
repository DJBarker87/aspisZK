from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));from NFF_source_checks import body
p=json.loads((E/'NFF_PAIRING_PAYLOAD.json').read_text());f=json.loads((E/'NFF_FROZEN.json').read_text());src=f['crates/aspis-r1-cost-probe/src/fast_pairing.rs']
a=src.index('impl EbyKDot {');part=src[a:];actual=body(part,'push');abstract=actual.replace('self.','receiver.')
for i in range(2):abstract=abstract.replace(f'receiver.c{i}.push(value_c{i}, scalar);',f'NFF_private_push(log,{i},&mut receiver.c{i},value_c{i},scalar);')
s=p['crates/aspis-r1-cost-probe/src/NFF_pairing.rs']
s+='''
struct NFF_PublicLog { calls:usize,half:[usize;2],receiver:[usize;2],before:[[u64;4];2],left:[[u32;4];2],right:[[u32;4];2],replies:[[u64;4];2] }
fn NFF_private_push(log:&mut NFF_PublicLog,half:usize,dot:&mut Dot,a:Q,b:Q) {
 let at=log.calls;log.calls+=1;log.half[at]=half;
 log.receiver[at]=dot as *mut Dot as usize;log.before[at]=dot.sums;
 log.left[at]=a.0;log.right[at]=b.0;dot.sums=log.replies[at];
}
fn NFF_public_push(receiver:&mut EbyKDot,value:E,scalar:QM31,log:&mut NFF_PublicLog)->Result<(),()> {
'''+abstract+'''
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn public_push_context() {
 let mut receiver=EbyKDot{c0:Dot{sums:kani::any()},c1:Dot{sums:kani::any()},count:kani::any()};
 let count=receiver.count;let old=[receiver.c0.sums,receiver.c1.sums];
 let pointer=[&mut receiver.c0 as *mut Dot as usize,&mut receiver.c1 as *mut Dot as usize];
 let value:E=kani::any();let scalar:QM31=kani::any();let limbs=value.to_limbs();
 let q=super::super::limbs_of(scalar);
 let valid=q[0]<P && q[1]<P && q[2]<P && q[3]<P;
 let mut log=NFF_PublicLog{calls:0,half:[99;2],receiver:[0;2],before:[[0;4];2],left:[[0;4];2],right:[[0;4];2],replies:kani::any()};
 let returned=NFF_public_push(&mut receiver,value,scalar,&mut log);
 let half:usize=kani::any();let lane:usize=kani::any();kani::assume(half<2 && lane<4);
 if count>=4096 || !valid {
  assert!(returned.is_err());assert_eq!(log.calls,0);assert_eq!(receiver.count,count);
  let observed=if half==0{receiver.c0.sums[lane]}else{receiver.c1.sums[lane]};
  assert_eq!(observed,old[half][lane]);
 } else {
  assert!(returned.is_ok());assert_eq!(log.calls,2);assert_eq!(receiver.count,count+1);
  assert_eq!(log.half[half],half);assert_eq!(log.receiver[half],pointer[half]);
  assert_eq!(log.before[half][lane],old[half][lane]);
  assert_eq!(log.left[half][lane],limbs[half*4+lane]);assert_eq!(log.right[half][lane],q[lane]);
  let observed=if half==0{receiver.c0.sums[lane]}else{receiver.c1.sums[lane]};
  let expected=log.replies[half][lane];
  assert_eq!(observed,if cfg!(NFF_wrong_public_push){expected^1}else{expected});
 }
}
'''
s=s.replace('use super::super::{EbyKDot,E,QM31};','use super::super::{EbyKDot,E,QM31,MAX_TERMS,checked_q};')
p['crates/aspis-r1-cost-probe/src/NFF_pairing.rs']=s
(E/'NFF_PUBLIC_PAYLOAD.json').write_text(json.dumps(p));(E/'NFF_pairing.rs.txt').write_text(s)
(E/'NFF_PUBLIC_FISSION.json').write_text(json.dumps(dict(original=actual,abstracted=abstract,unchanged_checks=True,source='4bb3b3f5:fast_pairing.rs::EbyKDot::push'),indent=2))
