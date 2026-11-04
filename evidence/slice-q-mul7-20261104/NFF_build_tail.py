from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));from NFF_source_checks import body
p=json.loads((E/'NFF_PUBLIC_FIXED_PAYLOAD.json').read_text());f=json.loads((E/'NFF_FROZEN.json').read_text());source=f['crates/aspis-r1-cost-probe/src/fast_dots.rs']
a=source.index('        let mut tail=');b=source.index('\n    \n}',a);original=source[a:b];tail=original
import re
pattern=r'tail\.push\((g\[[^;]+?)\)\.unwrap\(\);'
# Replace only the method call (including nested byte decoder) in source order.
positions=[];cursor=0
for i in range(3):
 a0=tail.index('tail.push(',cursor);end=tail.index(').unwrap();',a0)+len(').unwrap();');old=tail[a0:end]
 inner=old[len('tail.push('):-len(').unwrap();')]
 new=f'NFF_public_push(&mut tail,{inner},&mut logs[{i}]).unwrap();'
 tail=tail[:a0]+new+tail[end:];cursor=a0+len(new)
s=p['crates/aspis-r1-cost-probe/src/NFF_pairing.rs']
s+='''
fn NFF_log()->NFF_PublicLog {NFF_PublicLog{calls:0,half:[99;2],receiver:[0;2],before:[[0;4];2],left:[[0;4];2],right:[[0;4];2],replies:kani::any()}}
fn NFF_tail(q:&[u8;608],g:&[WideExact;29],slot:usize,value:WideExact,logs:&mut[NFF_PublicLog;3])->WideExact {
'''+tail+'''
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn tail_same_run_window() {
 let q:[u8;608]=kani::any();let g:[E;29]=kani::any();let slot:usize=kani::any();kani::assume(slot<4);
 let offsets=[slot*120+104,480+slot*32,496+slot*32];
 for at in offsets {for k in 0..4 {let j=at+k*4;let word=u32::from_le_bytes([q[j],q[j+1],q[j+2],q[j+3]]);kani::assume(word<P);}}
 let head:E=kani::any();for word in head.to_limbs(){kani::assume(word<P);}
 let mut logs=[NFF_log(),NFF_log(),NFF_log()];let out=NFF_tail(&q,&g,slot,head,&mut logs);
 let call:usize=kani::any();let half:usize=kani::any();let lane:usize=kani::any();
 kani::assume(call<3 && half<2 && lane<4);
 assert_eq!((logs[0].calls,logs[1].calls,logs[2].calls),(2,2,2));
 let coefficient=if call==0{28}else if call==1{26}else{27};
 assert_eq!(logs[call].left[half][lane],g[coefficient].to_limbs()[half*4+lane]);
 let at=offsets[call]+4*lane;let scalar=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 assert_eq!(logs[call].right[half][lane],scalar);
 let before=if call==0{0}else{logs[call-1].replies[half][lane]};
 assert_eq!(logs[call].before[half][lane],before);
 let last=logs[2].replies[half][lane];let sum=head.to_limbs()[4*half+lane]+reduce(last);
 let expected=if sum>=P{sum-P}else{sum};
 assert_eq!(out.to_limbs()[4*half+lane],if cfg!(NFF_wrong_tail_run){expected^1}else{expected});
 assert!(out.to_limbs()[4*half+lane]<P);
}
'''
s=s.replace('use super::super::{EbyKDot,E,QM31,MAX_TERMS,checked_q};','use super::super::{EbyKDot,E,QM31,MAX_TERMS,checked_q};\nuse aspis_core::field::{WideExact,M31};')
p['crates/aspis-r1-cost-probe/src/NFF_pairing.rs']=s;(E/'NFF_TAIL_PAYLOAD.json').write_text(json.dumps(p));(E/'NFF_pairing.rs.txt').write_text(s)
(E/'NFF_TAIL_FISSION.json').write_text(json.dumps(dict(original=original,abstracted=tail,head='Canonical same-run scalarFinish supplied at source cut; finish/add remain native'),indent=2)+'\n')
