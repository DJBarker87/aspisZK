"""Freeze private scratch source, append NHF-only child, retain exact KMX patch."""
from pathlib import Path
import subprocess,json,hashlib,time,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';B='/home/dombarker/project-offloads/codex-cx-candidate-prepare-20261106'
sha=lambda b:hashlib.sha256(b).hexdigest()
names=subprocess.check_output(['git','ls-tree','-r','--name-only',F,'crates','programs'],text=True).splitlines()+['Cargo.lock','Cargo.toml']
files={}; binary={}
for n in names:
 data=subprocess.check_output(['git','show',F+':'+n])
 try:files[n]=data.decode()
 except UnicodeDecodeError:binary[n]=sha(data)
original=files.copy()
C='crates/aspis-r1-cost-probe/src/'
files[C+'lib.rs']='#![cfg_attr(kani, feature(allocator_api))]\n'+files[C+'lib.rs']
files[C+'candidate.rs']+='\n#[cfg(kani)]\n#[path="NHF_wide.rs"]\nmod NHF_wide;\n'
files[C+'NHF_wide.rs']=(E/'NHF_wide.rs.txt').read_text()
pins={**binary,**{n:sha(t.encode()) for n,t in files.items()}};(E/'NHF_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
(E/'NHF_FROZEN_SOURCE_PINS.json').write_text(json.dumps({n:sha(t.encode()) for n,t in original.items()},indent=1)+'\n')
patch=''.join(''.join(difflib.unified_diff(original.get(n,'').splitlines(True),t.splitlines(True),fromfile='a/'+n if n in original else '/dev/null',tofile='b/'+n)) for n,t in files.items() if original.get(n)!=t)
(E/'NHF_native.patch').write_text(patch)
code=f'''from pathlib import Path
import json,subprocess,shutil,sys,hashlib
b=Path({B!r});p=b/'NHF_NATIVE_SETUP-admission.json'
with (b/'NHF_NATIVE_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING',flush=True)
if not p.exists():sys.exit(79)
if r.returncode!=0 or json.loads(p.read_text()).get('allowed') is not True:sys.exit(78)
s=b/'NHF_src';assert not s.exists()
shutil.copytree(b.parent/'codex-cx-slice-d-prepare-20261104/NFW_src',s,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
for n,t in json.loads({json.dumps(files)!r}).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NHF_SOURCE_PINS.json').write_text({json.dumps(pins)!r})
print(json.dumps(dict(files={len(files)},frozen={F!r},bytes=sum(p.stat().st_size for p in s.rglob('*') if p.is_file()))))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 (E/f'NHF_NATIVE_SETUP-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode==255 and retry<10:time.sleep(60);continue
 if r.returncode==78 and retry<10:time.sleep(180);continue
 if r.returncode==79 and retry==0:time.sleep(30);continue
 raise RuntimeError(r.stdout+r.stderr)
else:raise RuntimeError('admission exhausted')
print(r.stdout[-600:])
