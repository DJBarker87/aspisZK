from pathlib import Path
from NGO_inputs import load,write
import subprocess,json,hashlib,re
E=Path(__file__).resolve().parent
source=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/r1_semantic.rs'],text=True)
for expression in ['let row = 15 + round as u8;','record.decode_k::<29>(p * 29)?','for p in 0..3']:assert expression in source
inputs=load();n='crates/aspis-r1-cost-probe/src/NGO_q.rs'
inputs[n]+='''
#[kani::proof] fn NGO_round_domain() {
 let round:usize=kani::any();kani::assume(round<10);
 let row = 15 + round as u8;
 #[cfg(not(NGO_invert))] assert!(row as usize==15+round && row>=15 && row<=24);
 #[cfg(NGO_invert)] assert!(row==14);
}
#[kani::proof] fn NGO_claims_domain() {
 let p:usize=kani::any();kani::assume(p<3);
 let offset=p*29;
 #[cfg(not(NGO_invert))] assert!(offset+29<=116 && offset<=58);
 #[cfg(NGO_invert)] assert!(offset+29>116);
}
'''
write(inputs)
(E/'NGO_CALLER_SOURCE.json').write_text(json.dumps(dict(source_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_sha256=hashlib.sha256(source.encode()).hexdigest(),calls=[dict(N=int(m[1]),offset=m[2],line=source[:m.start()].count('\n')+1) for m in re.finditer(r'decode_k::<(\d+)>\(([^)]*)\)',source)],domain_scope='Native original scalar expressions only, not complete enclosing callers; source window/record facts established separately in Lean'),indent=2))
