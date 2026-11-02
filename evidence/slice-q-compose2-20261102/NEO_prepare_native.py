from NEO_remote import *
import hashlib
R=E.parent.parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
a='NEO_NATIVE_SETUP';admit(a)
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',REV,'crates','programs','Cargo.lock'],cwd=R,text=True).splitlines()
owned={n:subprocess.check_output(['git','show',REV+':'+n],cwd=R,text=True) for n in paths if n.endswith(('.rs','.toml')) or n=='Cargo.lock'}
payload=dict(owned=owned,patch=(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_text())
code=f'''from pathlib import Path
import json,subprocess,hashlib
x=json.loads({json.dumps(payload)!r});b=Path({B!r});s=b/'NEO_src';assert not s.exists();s.mkdir()
old=b.parent/'codex-cx-slice-q-compose-20261029/NEB_src'
for p in old.rglob('*'):
 if not p.is_file():continue
 n=str(p.relative_to(old))
 if any(v.startswith(('NEB_','NCO_','NCH_')) or v in ['target','.git'] for v in Path(n).parts):continue
 if n.startswith('KMX_'):continue
 q=s/n;q.parent.mkdir(parents=True,exist_ok=True)
 if n in x['owned']:q.write_text(x['owned'][n])
 elif p.name=='Cargo.toml':q.write_bytes(p.read_bytes())
 else:q.symlink_to(p.resolve())
for n,t in x['owned'].items():
 if (s/n).exists():continue
 if n.startswith(('crates/','programs/')) and not (s/Path(n).parts[0]/Path(n).parts[1]).exists():continue
 q=s/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(t)
patch=b/'NEO_KMX.patch';patch.write_text(x['patch']);subprocess.run(['git','apply',str(patch)],cwd=s,check=True)
(b/'NEO_tmp').mkdir(exist_ok=True)
print(json.dumps(dict(frozen_revision={REV!r},frozen_source_files=len(x['owned']),root_manifest=(s/'Cargo.toml').read_text(),lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),copy_patch_sha256=hashlib.sha256(patch.read_bytes()).hexdigest())))
'''
r=ssh(a,'python3',code);(E/'NEO_NATIVE_SETUP.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
print(r.stdout)
