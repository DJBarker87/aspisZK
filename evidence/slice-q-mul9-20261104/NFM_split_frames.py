from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'NFM_STRICT_PAYLOAD.json').read_text());key='crates/aspis-r1-cost-probe/src/NFM_dots.rs';s=p[key]
# Replace ONLY the timed-out supplementary frame harness shape. The original
# complete-window proofs remain in their immutable payload and receipts.
from NFM_source_checks import body
for cut in range(7):
 start=4*cut;end=min(start+4,26)
 replacement=f'''
 let q:[u8;608]=if cfg!(NFM_fixture){{[0;608]}}else{{kani::any()}};
 let g:[WideExact;29]=if cfg!(NFM_fixture){{[WideExact::ZERO;29]}}else{{kani::any()}};
 let slot:usize=kani::any();let term:usize=kani::any();let lane:usize=kani::any();
 let observed:usize=kani::any();let gi:usize=kani::any();
 kani::assume(slot<4 && {start}<=term && term<{end} && lane<8 && observed<608 && gi<29);
 let mut sums:[u64;8]=if cfg!(NFM_fixture){{[0;8]}}else{{kani::any()}};
 let limbs:[u64;8]=kani::any();let replies:[u64;8]=if cfg!(NFM_fixture){{[0;8]}}else{{kani::any()}};
 for j in 0..8{{kani::assume(sums[j]<=3*NFM_BOUND);kani::assume(replies[j]<=NFM_BOUND);}}
 let at=slot*120+term*4;let scalar=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 kani::assume(scalar<2147483647);
 let old_s=sums[lane];let old_l=limbs[lane];let saved=q[observed];let coeff=g[gi].to_limbs()[lane];
 let qp=q.as_ptr() as usize;let gp=g.as_ptr() as usize;
 let mut log=NFM_Log{{replies,left:[0;8],right:[0;8],calls:[0;8],order:[99;8],next:0}};
 NFM_step(&q,&g,slot,term,&mut sums,&mut log);
 assert_eq!(log.next,8);assert_eq!(log.calls[lane],1);
 assert_eq!(log.left[lane],g[term].to_limbs()[lane] ^ if cfg!(NFM_wrong_left){{1}}else{{0}});
 assert_eq!(log.right[lane],scalar ^ if cfg!(NFM_wrong_right){{1}}else{{0}});
 assert_eq!(log.order[lane],lane+if cfg!(NFM_wrong_order){{1}}else{{0}});
 assert_eq!(sums[lane],(old_s+replies[lane]) ^ if cfg!(NFM_wrong_sums){{1}}else{{0}});
 assert_eq!(q[observed],saved ^ if cfg!(NFM_wrong_frame){{1}}else{{0}});
 assert_eq!(g[gi].to_limbs()[lane],coeff);
 assert_eq!(q.as_ptr() as usize,qp);assert_eq!(g.as_ptr() as usize,gp);
 assert_eq!(limbs[lane],old_l ^ if cfg!(NFM_wrong_limbs){{1}}else{{0}});
'''
 a=s.index('{',s.index(f'fn window_{cut}()'));old=body(s,f'window_{cut}');s=s[:a+1]+replacement+s[a+1+len(old):]
s+='''
// NFM_split_frame: one native term from an arbitrary prestate; compose by
// NFI_InnerTrace induction, then the separate source-exact fold boundary.
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn fold_borrowed_frame(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();let sums:[u64;8]=kani::any();let mut limbs:[u64;8]=kani::any();
 for j in 0..8{kani::assume(limbs[j]<=6*10737418238u64);}
 let lane:usize=kani::any();let observed:usize=kani::any();let gi:usize=kani::any();kani::assume(lane<8 && observed<608 && gi<29);
 let byte=q[observed];let coeff=g[gi].to_limbs()[lane];let before=limbs[lane];
 NFM_fold(sums,&mut limbs);
 assert_eq!(limbs[lane],before+(sums[lane]&0x7fffffff)+(sums[lane]>>31));
 assert_eq!(g[gi].to_limbs()[lane],coeff);
 assert_eq!(q[observed],byte ^ if cfg!(NFM_wrong_fold_frame){1}else{0});
}
'''
f=json.loads((E.parent/'slice-q-mul7-20261104/NFF_FROZEN.json').read_text())['crates/aspis-r1-cost-probe/src/fast_dots.rs'];a=f.index('        let mut value =');b=f.index('        let mut tail=',a)
s+='fn NFM_head(limbs:[u64;8])->WideExact{\n'+f[a:b].replace('let mut value =','let value =')+'value\n}\n'
s+='''
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn head_borrowed_frame(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();let limbs:[u64;8]=kani::any();
 let lane:usize=kani::any();let observed:usize=kani::any();let gi:usize=kani::any();kani::assume(lane<8 && observed<608 && gi<29);
 let byte=q[observed];let coeff=g[gi].to_limbs()[lane];let out=NFM_head(limbs);
 assert_eq!(q[observed],byte);assert_eq!(g[gi].to_limbs()[lane],coeff);
 assert_eq!(out.to_limbs()[lane]<2147483647,!cfg!(NFM_wrong_head_frame));
}
'''
p[key]=s;(E/'NFM_SPLIT_FRAME_PAYLOAD.json').write_text(json.dumps(p))
(E/'NFM_K041_CLEANUP.json').write_text(json.dumps(dict(own_tmpdir='/home/dombarker/project-offloads/codex-cx-slice-q-mul9-20261104/NFM_tmp',removed=[],unowned_tmp_files_removed=False)))
