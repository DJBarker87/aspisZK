from NCN_extend import E,current,attrs
import difflib,json,subprocess,hashlib
s=current();start=s.index('fn read_checkpoint_semantic_alpha(');end=s.index('\n#[inline(never)]\npub fn resume',start)
original=s[start:end];assert original.count('r.k()?')==10
changed=original.replace('r.k()?', '{#[cfg(kani)] {NCN_semantic::observed(&mut r)} #[cfg(not(kani))] {r.k()}}?')
out=s[:start]+changed+s[end:]
h='''
#[cfg(kani)] mod NCN_semantic {
use super::*;
static mut CALLS:usize=0;
static mut INPUT:[usize;10]=[0;10];
static mut OUTPUT:[usize;10]=[0;10];
static mut GOOD:[bool;10]=[false;10];
static mut REPLY:[K;10]=[K::ZERO;10];
pub(super) fn observed(r:&mut Reader<'_>)->Result<K,Error>{
let i=unsafe{CALLS};assert!(i<10);unsafe{INPUT[i]=r.at;}
let out=r.k();
unsafe{OUTPUT[i]=r.at;if let Ok(v)=out {GOOD[i]=true;REPLY[i]=v;}CALLS+=1;}
out
}
'''
q=[]
for kind in ['order','values','errors']:
 for neg in [False,True]:
  name=kind+('_wrong' if neg else '_ok')
  h+=attrs+'#[kani::stub_verified(Reader::k)]\n'+f'''fn {name}(){{let bytes:[u8;1768]=kani::any();let out=read_checkpoint_semantic_alpha(&bytes,408);let calls=unsafe{{CALLS}};assert!(calls>=1&&calls<=10);let j:usize=kani::any();kani::assume(j<calls);\n'''
  op='!=' if neg else '=='
  if kind=='order':h+=f'''assert!(unsafe{{INPUT[j]}}{op}408+16*j);assert!(unsafe{{OUTPUT[j]}}==424+16*j);\n'''
  if kind=='values':h+=f'''if let Ok((values,at))=out{{assert!(calls==10&&at==568);assert!(values[j]{op}unsafe{{REPLY[j]}});assert!(unsafe{{GOOD[j]}});}}\n'''
  if kind=='errors':h+=f'''if out.is_err(){{assert!(unsafe{{GOOD[calls-1]}}{op}false);if j+1<calls{{assert!(unsafe{{GOOD[j]}});}}}}else{{assert!(calls==10);assert!(unsafe{{GOOD[j]}});}}\n'''
  h+='}\n';q.append(dict(harness='verifier::NCN_semantic::'+name,negative=neg))
h+='}\n';out+=h
(E/'NCN_semantic.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),out.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/verifier.rs',tofile='b/crates/aspis-r1-cost-probe/src/verifier.rs')))
for i,x in enumerate(q,42):x.update(attempt=f'NCN_K{i:03}',patch='NCN_semantic.patch')
(E/'NCN_semantic_queue.json').write_text(json.dumps(q,indent=2)+'\n')
(E/'NCN_SEMANTIC_SOURCE.json').write_text(json.dumps(dict(frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',original=original,sha256=hashlib.sha256(original.encode()).hexdigest(),instrumentation='Only k call sites wrap an actual k call and log its input, output cursor and reply; non-kani body byte-identical after cfg erasure.'),indent=2)+'\n')
