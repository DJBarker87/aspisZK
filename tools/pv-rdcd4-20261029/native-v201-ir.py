"""Optimized deployed-configuration LLVM support for op79 reachability only.
No machine-code or LLVM correspondence theorem, no b3p6-1 credit.
Expected time: cached optimized compilation, then one named IR-cone scan.
"""
from pathlib import Path
import json,os,subprocess,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028/rdcd4-20261029')
P=D/'classification-project-fixture';O=D/'native-v201-ir';O.mkdir(exist_ok=True)
old=(D/'classify-project-encoder/fixture.rs.txt').read_text()
wrapper='''
#[unsafe(no_mangle)]
pub fn pv_rdcd4_op79(q: &[aspis_core::field::WideExact;1024], p: Point<aspis_core::field::WideExact>) -> aspis_core::field::WideExact {
    aspis_core::r0::encoder::eval_message(q,p)
}
'''
source=old+wrapper;(P/'fixture.rs').write_text(source);(O/'fixture.rs.txt').write_text(source)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR='/home/dombarker/project-offloads/codex-pv-rdcd4-20261029/classification-target',CARGO_BUILD_JOBS='4')
command=['cargo','rustc','--manifest-path',str(P/'Cargo.toml'),'--release','--locked','--lib','-j','4','--','--emit=llvm-ir']
inputs=json.load(open(D/'classify-project-encoder/inputs.json'));inputs.update(command=command,expected_time='cached optimized compilation then op79 LLVM-cone scan',scope='Supporting deployed instantiation/guard reachability; no LLVM equivalence or b3p6-1 inference',fixture_sha256=hashlib.sha256(source.encode()).hexdigest(),prior_native_fixture_sha256=hashlib.sha256(old.encode()).hexdigest(),profile='release opt3 debug_assertions=false overflow_checks=false')
(O/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
r=subprocess.run(command,env=env);assert r.returncode==0,r.returncode
ll=list((D/'classification-target/release/deps').glob('pv_fscan_deployed_project_fixture-*.ll'));assert len(ll)==1,[str(p) for p in ll]
s=ll[0].read_text();blocks={}
for m in re.finditer(r'^define[^\n]*@([^ (]+)[^\n]*\{\n',s,re.M):
 end=s.index('\n}',m.end())+2;blocks[m[1]]=s[m.start():end]
assert 'pv_rdcd4_op79' in blocks
seen={};pending=['pv_rdcd4_op79'];external=set()
while pending:
 name=pending.pop()
 if name in seen:continue
 b=blocks[name];calls=re.findall(r'\b(?:call|invoke)\b[^\n]*?@([^ (]+)',b)
 seen[name]=dict(sha256=hashlib.sha256(b.encode()).hexdigest(),calls=calls)
 for c in calls:
  if c in blocks:pending.append(c)
  else:external.add(c)
notes={key:[name for name in seen if key in name] for key in ['panic','precondition','is_null','NonNull','GenericArray','BTree','simd']}
(O/'root.ll.txt').write_text(blocks['pv_rdcd4_op79']+'\n')
(O/'result.json').write_text(json.dumps(dict(ir_path=str(ll[0]),ir_sha256=hashlib.sha256(ll[0].read_bytes()).hexdigest(),ir_size=ll[0].stat().st_size,functions=seen,external_calls=sorted(external),diagnostic_symbol_hits=notes,scope=inputs['scope'],qualification='Absence of symbols supports this optimized wrapper only; source-level exclusion still requires the pinned source dispatch and bounds checks'),indent=2)+'\n')
print(json.dumps(dict(functions=len(seen),external_calls=sorted(external),diagnostic_hits=notes)))
