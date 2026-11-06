from NLF_transport import *
import base64,lzma,hashlib
sha=lambda b:hashlib.sha256(b).hexdigest()
old=E.parent/'entry-sdk-20261108'
idx=json.loads((old/'NJN_INPUTS.json').read_text()); files=idx['attempts']['NJN_K032']; inputs={}
for name in ['NGL_FROZEN_SOURCE_PINS.json']:
 raw=lzma.decompress((old/idx['objects'][files[name]]['path']).read_bytes());inputs[name]=raw.decode()
pins=json.loads(inputs['NGL_FROZEN_SOURCE_PINS.json']); frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
for name in pins:
 raw=subprocess.check_output(['git','show',frozen+':'+name]);assert sha(raw)==pins[name];inputs['NLF_src/'+name]=base64.b64encode(raw).decode()
patch=subprocess.check_output(['git','show','HEAD:evidence/kani-mitig-20261028/KMX_copy_stubs.patch'])
inputs['NLF_KMX_copy_stubs.patch']=patch.decode()
inputs['NLF_FROZEN_PINS.json']=inputs.pop('NGL_FROZEN_SOURCE_PINS.json')
raw=json.dumps(inputs).encode();(E/'NLF_FROZEN_INPUTS.json.xz').write_bytes(lzma.compress(raw));(E/'NLF_FROZEN_INPUTS.json.sha256').write_text(sha(raw)+'\n')
admission('NLF_NATIVE_SEED')
payload=base64.b64encode(lzma.compress(raw)).decode()
r=ssh('python3',f'''from pathlib import Path
import shutil,json,hashlib,lzma,base64,subprocess
b=Path({B!r});s=b/'NLF_src';assert not s.exists()
shutil.copytree('/home/dombarker/project-offloads/codex-cx-entry-sdk-20261108/NJN_src',s,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
files=json.loads(lzma.decompress(base64.b64decode({payload!r})))
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(t)) if n.startswith('NLF_src/') else p.write_text(t)
# Reapply the exact mitigation to a pristine set of mitigation files.
for n in ['KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean']:
 p=s/n
 if p.exists():p.unlink()
r=subprocess.run(['patch','-p1','-i',str(b/'NLF_KMX_copy_stubs.patch')],cwd=s,capture_output=True,text=True);assert r.returncode==0,r.stdout+r.stderr
pins=json.loads((b/'NLF_FROZEN_PINS.json').read_text());assert all(hashlib.sha256((s/n).read_bytes()).hexdigest()==h for n,h in pins.items())
print(json.dumps(dict(files=len(pins),source_revision={frozen!r},bytes=sum(p.stat().st_size for p in s.rglob('*') if p.is_file()),kmx_patch_sha256=hashlib.sha256((b/'NLF_KMX_copy_stubs.patch').read_bytes()).hexdigest(),lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),CARGO_TARGET_DIR=str(b/'NLF_target'))))
''');assert r.returncode==0,r.stderr
(E/'NLF_NATIVE_SEED.json').write_text(r.stdout)
print('NLF scratch seeded and 498 frozen inputs restored; exact KMX patch applied')
