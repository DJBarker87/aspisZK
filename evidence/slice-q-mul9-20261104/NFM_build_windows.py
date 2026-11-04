from pathlib import Path
import json
E=Path(__file__).resolve().parent
p=json.loads((E/'NFM_CONTROL_PAYLOAD.json').read_text());key='crates/aspis-r1-cost-probe/src/NFM_dots.rs'
s=p[key]
s+='''
struct NFM_WindowLog { replies:[[u64;8];4], left:[[u32;8];4], right:[u32;4], order:[usize;32], calls:usize }
fn NFM_window_product(log:&mut NFM_WindowLog,offset:usize,lane:usize,a:u32,b:u32)->u64{
 log.order[log.calls]=offset*8+lane;log.calls+=1;
 log.left[offset][lane]=a;log.right[offset]=b;log.replies[offset][lane]
}
'''
# Literal body fission: same parser, operands, source order, adds. Only product sites record.
start=s.index('                let scalar',s.index('fn NFM_step('));end=s.index('\n}',start)
body=s[start:end]
for lane in range(8):body=body.replace(f'NFM_product(log, {lane},',f'NFM_window_product(log,offset,{lane},')
s+='fn NFM_window_term(q:&[u8;608],g:&[WideExact;29],slot:usize,term:usize,offset:usize,sums:&mut[u64;8],log:&mut NFM_WindowLog){\n'+body+'\n}\n'
attr='''#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
'''
for cut in range(7):
 start=4*cut;stop=min(start+4,26);width=stop-start
 s+=attr+f'''fn window_{cut}(){{
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();let slot:usize=kani::any();kani::assume(slot<4);
 let mut limbs:[u64;8]=kani::any();let mut sums:[u64;8]=kani::any();
 let replies:[[u64;8];4]=kani::any();let lane:usize=kani::any();kani::assume(lane<8);
 for j in 0..8{{kani::assume(limbs[j]<=6*10737418238u64);kani::assume(sums[j]<={4-width}*NFM_BOUND);}}
 for off in 0..{width}{{
  let at=slot*120+({start}+off)*4;
  kani::assume(u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]])<2147483647);
  for j in 0..8{{kani::assume(replies[off][j]<=NFM_BOUND);}}
 }}
 let old_s=sums[lane];let old_l=limbs[lane];
 let mut log=NFM_WindowLog{{replies,left:[[0;8];4],right:[0;4],order:[99;32],calls:0}};
 for term in {start}..core::cmp::min({start}+4,26){{
  NFM_window_term(&q,&g,slot,term,term-{start},&mut sums,&mut log);
 }}
 let mut expected=old_s;
 for off in 0..{width}{{
  expected+=replies[off][lane];
  let at=slot*120+({start}+off)*4;
  assert_eq!(log.left[off][lane],g[{start}+off].to_limbs()[lane]);
  assert_eq!(log.right[off],u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]));
  assert_eq!(log.order[off*8+lane],off*8+lane);
 }}
 assert_eq!(log.calls,{width}*8);assert_eq!(sums[lane],expected);
 NFM_fold(sums,&mut limbs);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_window_{cut}){{(old_l+(expected&0x7fffffff)+(expected>>31))^1}}else{{old_l+(expected&0x7fffffff)+(expected>>31)}});
}}
'''
p[key]=s
(E/'NFM_WINDOW_PAYLOAD.json').write_text(json.dumps(p));(E/'NFM_windows.rs.txt').write_text(s)
