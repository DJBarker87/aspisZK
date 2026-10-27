"""Static freeze + exact cumulative scratch patch; no build or shared mutation."""
from pathlib import Path
import subprocess,json,hashlib,shlex,time,difflib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-leaf-p6-15-20261027/LPq_src';R='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
prior=json.loads(Path('evidence/leaf-p6-11-20261027/LPm_SOURCE_AUDIT.json').read_text());files=list(prior['files'])
markers={'crates/aspis-r1-cost-probe/src/fast_pairing.rs':['\n    #[cfg(kani)] #[path="LPm_pairing.rs"] mod LPm_pairing;\n'],'crates/aspis-r1-cost-probe/src/lib.rs':['\n#[cfg(kani)] mod LPi_contracts;\n'],'crates/aspis-r1-cost-probe/src/verifier.rs':['\n#[cfg(kani)] #[path="LPi_verifier.rs"] mod LPi_verifier;\n','\n#[cfg(kani)] #[path="LPm_verifier.rs"] mod LPm_verifier;\n','\n#[cfg(kani)] #[path="LPq_verifier.rs"] mod LPq_verifier;\n']}
new=['crates/aspis-r1-cost-probe/src/'+x for x in ['LPi_contracts.rs','LPi_verifier.rs','LPm_verifier.rs','LPq_verifier.rs','fast_pairing/canonical/LPm_pairing.rs']]
script=f'''from pathlib import Path
import hashlib,json
b=Path({B!r});out={{}}
for n in {files!r}:
 p=b/n;data=p.read_bytes();norm=data
 for marker in {markers!r}.get(n,[]):
  m=marker.encode();assert norm.count(m)==1,(n,'registration count');norm=norm.replace(m,b'\\n')
 if n in {markers!r}:norm=norm.rstrip(b'\\n')+b'\\n'
 out[n]=dict(sha256=hashlib.sha256(data).hexdigest(),normalized_sha256=hashlib.sha256(norm).hexdigest(),bytes=len(data))
print(json.dumps(dict(files=out,overlay={{n:(b/n).read_text() for n in {list(markers)+new!r}}})))
'''
for trial in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],capture_output=True,text=True)
 with (E/'LPq_FREEZE_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=trial,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if trial<10:time.sleep(60)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout);errors=[]
for n,x in out['files'].items():
 x['frozen_sha256']=prior['files'][n]['frozen_sha256']
 if x['normalized_sha256']!=x['frozen_sha256']:errors.append([n,'scratch drift'])
 if hashlib.sha256(Path(n).read_bytes()).hexdigest()!=x['frozen_sha256']:errors.append([n,'repository drift'])
patch=''
for n,s in out['overlay'].items():
 before=Path(n).read_text().splitlines(keepends=True) if n in markers else []
 patch+=''.join(difflib.unified_diff(before,s.splitlines(keepends=True),fromfile='a/'+n if before else '/dev/null',tofile='b/'+n))
(E/'LPq_harness.patch').write_text(patch)
rc=json.loads((E/'LPq_K001/receipt.json').read_text());snapshot_check={}
for name,h in rc['source_hashes'].items():
 n=name.removeprefix('LPq_src/');actual=out['overlay'].get(n)
 got=hashlib.sha256(actual.encode()).hexdigest() if actual is not None else out['files'][n]['sha256']
 snapshot_check[name]=dict(receipt_sha256=h,current_sha256=got,match=h==got)
 if h!=got:errors.append([name,'run source changed'])
report=dict(frozen_revision=R,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),files=out['files'],errors=errors,kani_snapshot_check=snapshot_check,patch_sha256=hashlib.sha256(patch.encode()).hexdigest(),validation='Exact frozen sources normalized ONLY listed cfg(kani) registrations; no compilation')
(E/'LPq_FREEZE.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(files=len(files),errors=errors,patch_sha256=report['patch_sha256'])));assert not errors
