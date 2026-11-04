from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
p=json.loads((E/'NFM_PAYLOAD.json').read_text())
f=json.loads((E.parent/'slice-q-mul7-20261104/NFF_FROZEN.json').read_text())['crates/aspis-r1-cost-probe/src/fast_dots.rs']
# Preserve both actual loop headers, replacing values only at the ruled cuts.
outer=re.search(r'for start in .*? \{',f).group()
inner=re.search(r'for term in .*? \{',f).group()
s='''
struct NFM_ControlLog { pairs:[(usize,usize);26], starts:[usize;7], terms:usize, cuts:usize }
fn NFM_record(log:&mut NFM_ControlLog,start:usize,term:usize){
 log.pairs[log.terms]=(start,term);log.terms+=1;
}
fn NFM_control(log:&mut NFM_ControlLog){
'''+outer+'''
 log.starts[log.cuts]=start; log.cuts+=1;
 '''+inner+'''
 NFM_record(log,start,term);
 }
 }
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn control_trace(){
 let mut log=NFM_ControlLog{pairs:[(99,99);26],starts:[99;7],terms:0,cuts:0};
 NFM_control(&mut log);
 let i:usize=kani::any();kani::assume(i<26);
 let j:usize=kani::any();kani::assume(j<7);
 assert_eq!(log.terms,26);assert_eq!(log.cuts,7);
 assert_eq!(log.starts[j],j*4);
 assert_eq!(log.pairs[i],if cfg!(NFM_wrong_control){((i/4)*4,i+1)}else{((i/4)*4,i)});
}
'''
p['crates/aspis-r1-cost-probe/src/NFM_dots.rs']+=s
(E/'NFM_CONTROL_PAYLOAD.json').write_text(json.dumps(p))
(E/'NFM_control.rs.txt').write_text(s)
(E/'NFM_CONTROL_SOURCE.json').write_text(json.dumps(dict(frozen_sha256=hashlib.sha256(f.encode()).hexdigest(),outer=outer,inner=inner,cut_count=7,term_count=26,qualification='Control only under ruling (ad); no value credit'),indent=2))
