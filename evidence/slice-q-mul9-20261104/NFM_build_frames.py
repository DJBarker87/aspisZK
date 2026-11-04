from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'NFM_WRAPPER_PAYLOAD.json').read_text());key='crates/aspis-r1-cost-probe/src/NFM_dots.rs';s=p[key]
a=s.index('fn window_0()');b=s.index('// Expose the frozen',a)
section=s[a:b]
section=section.replace('let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();','let q:[u8;608]=if cfg!(NFM_fixture){[0;608]}else{kani::any()};let g:[WideExact;29]=if cfg!(NFM_fixture){[WideExact::ZERO;29]}else{kani::any()};')
section=section.replace('let mut limbs:[u64;8]=kani::any();let mut sums:[u64;8]=kani::any();','let mut limbs:[u64;8]=if cfg!(NFM_fixture){[0;8]}else{kani::any()};let mut sums:[u64;8]=if cfg!(NFM_fixture){[0;8]}else{kani::any()};')
section=section.replace('let replies:[[u64;8];4]=kani::any();','let replies:[[u64;8];4]=if cfg!(NFM_fixture){[[0;8];4]}else{kani::any()};')
section=section.replace('let old_s=sums[lane];let old_l=limbs[lane];','let old_s=sums[lane];let old_l=limbs[lane];\n let observed:usize=kani::any();let gi:usize=kani::any();kani::assume(observed<608 && gi<29);\n let saved=q[observed];let coeff=g[gi].to_limbs()[lane];\n let qp=q.as_ptr() as usize;let gp=g.as_ptr() as usize;')
for cut in range(7):
 start=4*cut;width=min(4,26-start)
 section=section.replace(f'assert_eq!(log.left[off][lane],g[{start}+off].to_limbs()[lane]);',f'assert_eq!(log.left[off][lane],g[{start}+off].to_limbs()[lane] ^ if cfg!(NFM_wrong_left){{1}}else{{0}});')
 section=section.replace(f'assert_eq!(log.calls,{width}*8);',f'assert_eq!(log.calls,{width}*8+if cfg!(NFM_wrong_calls){{1}}else{{0}});')
section=section.replace('assert_eq!(log.right[off],u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]));','assert_eq!(log.right[off],u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]) ^ if cfg!(NFM_wrong_right){1}else{0});')
section=section.replace('assert_eq!(log.order[off*8+lane],off*8+lane);','assert_eq!(log.order[off*8+lane],off*8+lane+if cfg!(NFM_wrong_order){1}else{0});')
section=section.replace('assert_eq!(sums[lane],expected);','assert_eq!(sums[lane],expected ^ if cfg!(NFM_wrong_sums){1}else{0});\n assert_eq!(q[observed],saved ^ if cfg!(NFM_wrong_frame){1}else{0});assert_eq!(g[gi].to_limbs()[lane],coeff);\n assert_eq!(q.as_ptr() as usize,qp);assert_eq!(g.as_ptr() as usize,gp);')
s=s[:a]+section+s[b:];p[key]=s;(E/'NFM_FRAME_PAYLOAD.json').write_text(json.dumps(p))
