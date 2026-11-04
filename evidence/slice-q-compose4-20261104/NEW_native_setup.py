from NEW_remote import *
import hashlib,difflib,tarfile,io
R=E.parent.parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
a='NEW_NATIVE_SETUP';admit(a)
raw=subprocess.check_output(['git','archive',REV,'crates','programs','Cargo.lock'],cwd=R)
with tarfile.open(fileobj=io.BytesIO(raw)) as tar:
 owned={m.name:tar.extractfile(m).read().decode() for m in tar.getmembers() if m.isfile() and (m.name.endswith(('.rs','.toml')) or m.name=='Cargo.lock')}
x=dict(owned=owned,patch=(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_text())
r=ssh(a,'python3',f"""from pathlib import Path
import json,shutil,hashlib,subprocess
x=json.loads({json.dumps(x)!r});b=Path({B!r});s=b/'NEW_src';assert not (s/'Cargo.lock').exists()
old=b.parent/'codex-cx-slice-q-compose3-20261102/NET_src'
shutil.copytree(old,s,dirs_exist_ok=True,symlinks=True,ignore=shutil.ignore_patterns('target','.git'))
for n,t in x['owned'].items():
 p=s/n
 if p.is_symlink():p.unlink()
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
# KMX patch already exists in the copied scratch; check byte identity rather than reapply.
patch=b/'NEW_KMX.patch';patch.write_text(x['patch'])
subprocess.run(['git','apply','--reverse','--check',str(patch)],cwd=s,check=True)
(b/'NEW_tmp').mkdir(exist_ok=True)
# Copy generated NEO child objects omitted by the flat setup glob, retaining provenance.
c=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose4-cache-20261029')
imports=json.loads((b/'NEW_CACHE_IMPORTS.json').read_text())
for p in (b.parent/'codex-cx-slice-q-compose2-20261102').rglob('*.olean*'):
 rel=p.relative_to(b.parent/'codex-cx-slice-q-compose2-20261102')
 if not rel.parts[0].startswith('NEO_'):continue
 q=c/rel
 if not q.exists():q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
 imports[str(p)]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),selected_path=str(q),selected_sha256=hashlib.sha256(q.read_bytes()).hexdigest())
(b/'NEW_CACHE_IMPORTS.json').write_text(json.dumps(imports,indent=1)+'\\n')
print(json.dumps(dict(frozen_revision={REV!r},files=len(x['owned']),lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),KMX_sha256=hashlib.sha256(patch.read_bytes()).hexdigest())))
""")
(E/'NEW_NATIVE_SETUP.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
r=ssh(a,'cat '+B+'/NEW_CACHE_IMPORTS.json');assert r.returncode==0;(E/'NEW_CACHE_IMPORTS.json').write_text(r.stdout)
print('Private frozen source and generated cache objects prepared')
