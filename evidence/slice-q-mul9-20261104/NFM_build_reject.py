from pathlib import Path
import json
E=Path(__file__).resolve().parent
p=json.loads((E/'NFM_WINDOW_PAYLOAD.json').read_text());key='crates/aspis-r1-cost-probe/src/NFM_dots.rs';s=p[key]
s+='''
// Expose the frozen scalar unwrap terminal as an explicit abort tag. No
// coefficient read/product/fold is executed on that terminal branch.
fn NFM_read_or_abort(q:&[u8;608],slot:usize,term:usize)->Result<M31,usize>{
 match M31::from_le_bytes(q[slot*120+term*4..slot*120+term*4+4].try_into().unwrap()){
  Some(s)=>Ok(s),None=>Err(term)
 }
}
'''
attr='''#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
'''
for cut in range(7):
 start=4*cut;stop=min(start+4,26)
 s+=attr+f'''fn reject_{cut}(){{
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();
 let slot:usize=kani::any();let term:usize=kani::any();let lane:usize=kani::any();
 kani::assume(slot<4 && {start}<=term && term<{stop} && lane<8);
 let mut sums:[u64;8]=kani::any();let limbs:[u64;8]=kani::any();
 let old_s=sums[lane];let old_l=limbs[lane];let mut calls=0;
 let at=slot*120+term*4;let word=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 kani::assume(word>=2147483647);
 let terminal=match NFM_read_or_abort(&q,slot,term){{
  Err(t)=>{{assert_eq!(t,term);true}},
  Ok(s)=>{{let c=g[term].to_limbs();calls+=1;sums[lane]=u64::from(c[lane])+u64::from(s.0);false}}
 }};
 assert!(terminal);assert_eq!(calls,0);assert_eq!(sums[lane],old_s);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_reject_{cut}){{old_l^1}}else{{old_l}});
}}
'''
p[key]=s;(E/'NFM_REJECT_PAYLOAD.json').write_text(json.dumps(p));(E/'NFM_reject.rs.txt').write_text(s[s.index('// Expose the frozen'):])
