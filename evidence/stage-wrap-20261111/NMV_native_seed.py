from NMV_transport import *
import base64,hashlib
# Correct amended Pool files from Git; no sibling scratch source is used.
paths=subprocess.check_output(['git','ls-tree','-r','--name-only','b936275465','programs/aspis-pool'],text=True).splitlines()
pool={n:base64.b64encode(subprocess.check_output(['git','show','b936275465:'+n])).decode() for n in paths}
patch=(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
(E/'NMV_KMX_copy_stubs.patch').write_text(patch)
(E/'NMV_KMX_copy_stubs.patch.sha256').write_text(hashlib.sha256(patch.encode()).hexdigest()+'\n')
r=ssh('python3',f'''from pathlib import Path
import base64,json,hashlib,subprocess,shutil
b=Path({B!r});s=b/'NMV_src'
for p in (s/'programs/aspis-pool').rglob('*'):
 if p.is_file():p.unlink()
for n,v in json.loads({json.dumps(pool)!r}).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(v))
p=b/'NMV_KMX_copy_stubs.patch';p.write_text({patch!r})
shutil.copy2(p,b/'NMV_expected_KMX.patch')
r=subprocess.run(['patch','-p1','--forward','-i',str(p)],cwd=s,capture_output=True,text=True)
assert r.returncode==0,r.stdout+r.stderr
manifest=json.loads((b/'NMV_STAGING_MANIFEST.json').read_text());pins={{}}
for n,v in manifest['files'].items():
 if n.startswith('programs/aspis-pool/'):continue
 pins[n]=v['sha256']
for n in json.loads({json.dumps(pool)!r}):pins[n]=hashlib.sha256((s/n).read_bytes()).hexdigest()
(b/'NMV_FROZEN_PINS.json').write_text(json.dumps(pins))
(b/'NMV_EXTRA_PINS.json').write_text('{{}}')
print(json.dumps(dict(files=len(pins),pool_revision='b936275465',lock=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),kmx_patch_sha256=hashlib.sha256(p.read_bytes()).hexdigest())))
''');assert r.returncode==0,r.stderr
(E/'NMV_NATIVE_SEED.json').write_text(r.stdout);print(r.stdout)
