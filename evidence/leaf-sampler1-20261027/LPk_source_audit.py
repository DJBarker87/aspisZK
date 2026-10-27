"""Check frozen scratch inputs, isolated fragments, and source association."""
from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-sampler1-20261027'
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
paths=['Cargo.toml','Cargo.lock','crates','programs','audit/poseidon-pair-probe/program','xtask','docs/research/v8-r0-zk-20261009/refine','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3','tools/r1-builder-reference']
entries=subprocess.check_output(['git','ls-tree','-r',rev,'--',*paths],text=True).splitlines()
remote="""from pathlib import Path
import json,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-leaf-sampler1-20261027/LPk_src')
print(json.dumps({str(p.relative_to(b)):hashlib.sha256(p.read_bytes()).hexdigest() for p in b.rglob('*') if p.is_file()}))
"""
actual=json.loads(subprocess.check_output(['ssh',H,'python3 - <<\'PY\'\n'+remote+'\nPY']))
expected={}
for l in entries:
 meta,path=l.split('\t');typ,sha=meta.split()[1:]
 if typ!='blob':continue
 expected[path]=hashlib.sha256(subprocess.check_output(['git','cat-file','blob',sha])).hexdigest()
errors=[]
for path,h in expected.items():
 if path=='crates/aspis-r1-cost-probe/src/sampler.rs':continue
 if actual.get(path)!=h:errors.append(path)
sp='crates/aspis-r1-cost-probe/src/sampler.rs';native=subprocess.check_output(['git','show',rev+':'+sp])
assert native.count(b'for limb in quotient.iter_mut().rev()')==1
assert b'*limb = (dividend / u64::from(P)) as u32;' in native
added=b'\n#[cfg(kani)] #[path = "LPk_harness.rs"] mod LPk_harness;\n'
assert actual[sp]==hashlib.sha256(native+added).hexdigest()
assert not errors,errors
out={'frozen_revision':rev,'expected_files':len(expected),'errors':errors,'frozen_lock_sha256':expected['Cargo.lock'],'frozen_sampler_sha256':expected[sp],'scratch_sampler_sha256':actual[sp],'only_frozen_file_change':'cfg(kani) module declaration appended to sampler.rs','scratch_added_files':[p for p in actual if p not in expected],'source_association':{'step':'sampler.rs:62-64, same pack/divide/cast/remainder expressions; assignment factored into q return for isolated gate','loop':'sampler.rs:61-65; same iter_mut().rev() traversal, limb store and remainder capture, arithmetic replaced by paired step stub','from_fn':'sampler.rs:59-67; core::array::from_fn call over eight results with one shared mutable quotient capture; arbitrary body in library-order gate','final_return':'sampler.rs:70-72, quotient[0]; Lean low_word and bound 256 identify its value'},'file_sha256':expected}
(E/'LPk_SOURCE.json').write_text(json.dumps(out,indent=2)+'\n')
