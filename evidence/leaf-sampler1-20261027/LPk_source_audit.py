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
harness=subprocess.check_output(['ssh',H,'cat '+B+'/LPk_src/crates/aspis-r1-cost-probe/src/LPk_harness.rs'],text=True)
import re
def compact(s):return re.sub(r'\s+','',s)
def body(text,name):
 pos=text.index('fn '+name+'(');start=text.index('{',pos);level=0
 for k in range(start,len(text)):
  if text[k]=='{':level+=1
  if text[k]=='}':level-=1
  if level==0:return text[start+1:k]
 raise AssertionError('unclosed function')
nb=body(native.decode(),'low_base_p_digits')
start=nb.index('let dividend =');end=nb.index('\n        }',start)
step=nb[start:end].strip().replace('u64::from(*limb)','u64::from(limb)').replace('*limb =','let q =').replace('remainder = dividend %','let r = dividend %')+'\n(q,r)'
assert compact(step)==compact(body(harness,'LPk_step'))
decode='core::array::from_fn(|i|u32::from_le_bytes(block[4*i..4*i+4].try_into().unwrap()))'
assert decode in compact(nb) and decode in compact(body(harness,'LPk_byte_decode'))
assert 'letdigits=core::array::from_fn(|_|{' in compact(nb)
assert 'forlimbinquotient.iter_mut().rev(){' in compact(nb)
for gate in ['LPk_reverse_order','LPk_reverse_store']:
 hb=compact(body(harness,gate))
 assert 'forlimbinquotient.iter_mut().rev(){' in hb
 assert 'let(q,r)=LPk_step(remainder,*limb);*limb=q;remainder=r;' in hb
assert '(digits,quotient[0])' in compact(nb)
assert native.count(b'for limb in quotient.iter_mut().rev()')==1
assert b'*limb = (dividend / u64::from(P)) as u32;' in native
added=b'\n#[cfg(kani)] #[path = "LPk_harness.rs"] mod LPk_harness;\n'
assert actual[sp]==hashlib.sha256(native+added).hexdigest()
assert not errors,errors
out={'frozen_revision':rev,'expected_files':len(expected),'errors':errors,'frozen_lock_sha256':expected['Cargo.lock'],'frozen_sampler_sha256':expected[sp],'scratch_sampler_sha256':actual[sp],'only_frozen_file_change':'cfg(kani) module declaration appended to sampler.rs','scratch_added_files':[p for p in actual if p not in expected],'scratch_harness_sha256':actual['crates/aspis-r1-cost-probe/src/LPk_harness.rs'],'source_association':{'step':'sampler.rs:62-64, same pack/divide/cast/remainder expressions; assignment factored into q return for isolated gate','loop':'sampler.rs:61-65; same iter_mut().rev() traversal, limb store and remainder capture, arithmetic replaced by paired step stub','from_fn':'sampler.rs:59-67; core::array::from_fn call over eight results with one shared mutable quotient capture; arbitrary body in library-order gate','final_return':'sampler.rs:70-72, quotient[0]; Lean low_word and bound 256 identify its value'},'exact_step_fragment_match':True,'exact_byte_decoder_match':True,'traversal_store_sequence_match':True,'file_sha256':expected}
(E/'LPk_SOURCE.json').write_text(json.dumps(out,indent=2)+'\n')
