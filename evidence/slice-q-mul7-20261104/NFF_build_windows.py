from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent;f=json.loads((E/'NFF_FROZEN.json').read_text());source=f['crates/aspis-r1-cost-probe/src/fast_dots.rs']
a=source.index('            for term in start..');a=source.index('                let scalar',a);b=source.index('\n            }',a)
body=source[a:b]
for i in range(8):
 old=f'u64::from(coefficient[{i}]) * u64::from(scalar.0)'
 assert body.count(old)==1
 body=body.replace(old,f'NFF_product(log, {i}, coefficient[{i}], scalar.0)')
r='''use super::*;
const NFF_BOUND:u64=4611686009837453316; // (P-1)^2
struct NFF_Log { replies:[u64;8],left:[u32;8],right:[u32;8],calls:[u8;8] }
fn NFF_product(log:&mut NFF_Log,lane:usize,a:u32,b:u32)->u64 {
 log.left[lane]=a;log.right[lane]=b;log.calls[lane]+=1;log.replies[lane]
}
fn NFF_step(q:&[u8;608],g:&[WideExact;29],slot:usize,term:usize,sums:&mut[u64;8],log:&mut NFF_Log) {
'''+body+'''
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn main_term_window() {
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();
 let slot:usize=kani::any();let term:usize=kani::any();let lane:usize=kani::any();
 kani::assume(slot<4 && term<26 && lane<8);
 let at=slot*120+term*4;
 let scalar=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 kani::assume(scalar<2147483647);
 let mut sums:[u64;8]=kani::any();let replies:[u64;8]=kani::any();
 for i in 0..8 {kani::assume(sums[i]<=3*NFF_BOUND);kani::assume(replies[i]<=NFF_BOUND);}
 let before=sums[lane];let byte=q[at];let coefficient=g[term].to_limbs()[lane];
 let mut log=NFF_Log{replies,left:[0;8],right:[0;8],calls:[0;8]};
 NFF_step(&q,&g,slot,term,&mut sums,&mut log);
 assert_eq!(log.calls[lane],1);
 assert_eq!(log.left[lane],coefficient);assert_eq!(log.right[lane],scalar);
 assert_eq!(q[at],byte);assert_eq!(g[term].to_limbs()[lane],coefficient);
 let expected=before+replies[lane];
 assert_eq!(sums[lane],if cfg!(NFF_wrong_main_term){expected^1}else{expected});
}
'''
(E/'NFF_dots.rs.txt').write_text(r)
p=json.loads((E/'NFF_PAYLOAD.json').read_text());p['crates/aspis-r1-cost-probe/src/NFF_dots.rs']=r;(E/'NFF_PAYLOAD.json').write_text(json.dumps(p))
# Exact fission certificate: original statements retained in original order;
# only the eight declared arithmetic sites replaced by local-record opaque calls.
assert body.count('NFF_product(log,')==8
rev=body
for i in range(8):rev=rev.replace(f'NFF_product(log, {i}, coefficient[{i}], scalar.0)',f'u64::from(coefficient[{i}]) * u64::from(scalar.0)')
assert rev==source[a:b]
(E/'NFF_SOURCE_FISSION.json').write_text(json.dumps(dict(frozen_sha256=hashlib.sha256(source.encode()).hexdigest(),original=source[a:b],abstracted=body,reverse_equal=True,qualification='One arbitrary inner-loop prestate; native induction/physical whole-call installation remains open. Products use NEG_ProductAbstraction, never Kani multiplication.'),indent=2)+'\n')
