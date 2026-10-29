from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
initial=json.loads((E/'NDI_SOURCE.json').read_text())['source_sha256'];canonical={}
for name in initial:
 if name.endswith('.rs') and name.startswith(('crates/','programs/')):
  r=subprocess.run(['git','show',F+':'+name],capture_output=True)
  if r.returncode==0:canonical[name]=r.stdout.decode()
code='''from pathlib import Path
import json,hashlib,difflib
b=Path('/home/dombarker/project-offloads/codex-cx-native-front3b-20261028');s=b/'NDI_src';initial=json.loads(INITIAL);canonical=json.loads(CANONICAL)
sha=lambda data:hashlib.sha256(data).hexdigest()
drift=[];diffs=[];before=[];copied=[];removed=[]
for p in list(s.rglob('*')):
 if not (p.is_file() or p.is_symlink()):continue
 name=str(p.relative_to(s));data=p.read_bytes()
 if name in initial and sha(data)!=initial[name] and not p.name.startswith('NDI_'):
  drift.append(dict(path=name,expected=initial[name],actual=sha(data),resolved=str(p.resolve()),mtime_ns=p.stat().st_mtime_ns))
  if name in canonical:diffs+=difflib.unified_diff(canonical[name].splitlines(True),data.decode().splitlines(True),fromfile='a/'+name,tofile='b/'+name,n=0)
 if name in canonical:
  if p.is_symlink():before.append(dict(path=name,resolved=str(p.resolve())));p.unlink()
  p.write_text(canonical[name]);copied.append(name)
 elif p.is_symlink():
  if p.suffix=='.rs' and not p.name.startswith(('NDI_','KMX_')):p.unlink();removed.append(name);continue
  assert name in initial and sha(data)==initial[name],('unfrozen extra',name)
  before.append(dict(path=name,resolved=str(p.resolve())));p.unlink();p.write_bytes(data);copied.append(name)
assert not [str(p) for p in s.rglob('*') if p.is_symlink()]
(b/'NDI_SOURCE_DRIFT.patch').write_text(''.join(diffs))
last=b/'NDI_K055/receipt.json'
print(json.dumps(dict(drift=drift,private_copies=len(copied),removed_own_orphan_symlinks=removed,prior_external_links=before,last_native_receipt_mtime_ns=last.stat().st_mtime_ns,first_refusal_mtime_ns=(b/'NDI_K056-source-check.json').stat().st_mtime_ns,shared_files_written=False,source_patch='NDI_SOURCE_DRIFT.patch')))
'''.replace('json.loads(INITIAL)','json.loads('+repr(json.dumps(initial))+')').replace('json.loads(CANONICAL)','json.loads('+repr(json.dumps(canonical))+')')
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);(E/'NDI_ISOLATION.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NDI_ISOLATION.json').write_text(json.dumps(x,indent=2)+'\n')
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat','/home/dombarker/project-offloads/codex-cx-native-front3b-20261028/NDI_SOURCE_DRIFT.patch'],capture_output=True,text=True);assert r.returncode==0,r.stderr;(E/'NDI_SOURCE_DRIFT.patch').write_text(r.stdout)
print(json.dumps({k:v for k,v in x.items() if k!='prior_external_links'}))
