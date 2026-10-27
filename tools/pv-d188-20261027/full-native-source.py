from pathlib import Path
import json,hashlib
out=Path('evidence/pv-d188-20261027');d=out/'tests/native2-files';bindings=[]
def item(p,n):
 t=Path(p).read_text();a=t.index(n);b=t.index('{',a);depth=1;i=b+1
 while depth:
  if t[i]=='{':depth+=1
  elif t[i]=='}':depth-=1
  i+=1
 s=t[a:i];bindings.append(dict(path=p,line=t.count('\n',0,a)+1,sha256=hashlib.sha256(s.encode()).hexdigest()));return s
s='const STATE_ONLY_POSEIDON_TRACE_ROWS:usize=1024;const STATE_ONLY_HIDING_C1_COLUMNS:usize=16;const MAX_BATCH:usize=16;\n'
s+='mod verifier{#[derive(Debug)]'+item('crates/aspis-r1-cost-probe/src/verifier.rs','pub enum Error')+'}\n'
for p,n in [('crates/aspis-prover/src/state_only_hiding.rs','fn active_rows('),('crates/aspis-prover/src/state_only_entropy.rs','fn source_active_flags('),('crates/aspis-prover/src/state_only_hiding.rs','fn mask_dependent_step('),('crates/aspis-r1-cost-probe/src/host_tree.rs','fn count_level('),('crates/aspis-r1-cost-probe/src/host_tree.rs','fn count_parent('),('crates/aspis-r1-cost-probe/src/host_transcript.rs','fn query_contains('),('crates/aspis-r1-cost-probe/src/host_transcript.rs','fn scan_query_words(')]:s+=item(p,n)+'\n'
s+='''fn main(){println!("active {:?}",&active_rows(&[1,3,7])[..8]);println!("flags {:?}",&source_active_flags(&[1;64])[..32]);println!("dependent {:?}",mask_dependent_step([None;16],3,7,false)[3]);let mut a=[0;16];a[..3].copy_from_slice(&[1,2,3]);println!("count {:?}",count_level(a,3));let mut b=[0;32];b[0]=2;println!("scan {:?}",scan_query_words(&[b;8],&[[7;32];8],[1;22],21,0).unwrap());}\n'''
(d/'native6.rs').write_text(s);(out/'native7-source-binding.json').write_text(json.dumps(dict(fragments=bindings,constants=dict(STATE_ONLY_POSEIDON_TRACE_ROWS=1024,STATE_ONLY_HIDING_C1_COLUMNS=16,MAX_BATCH=16),note='Exact source bodies; no foreign callbacks or arithmetic stubs.'),indent=2)+'\n')
p=Path('tools/pv-d188-20261027/native.py');t=p.read_text().replace("'native-006':'native2-files/native5.rs'","'native-006':'native2-files/native5.rs','native-007':'native2-files/native6.rs'");p.write_text(t)
