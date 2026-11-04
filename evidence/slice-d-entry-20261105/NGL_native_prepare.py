"""Scratch source inputs; frozen bodies retained, own harnesses only."""
from pathlib import Path
import subprocess,json,hashlib,difflib,base64,time
E=Path(__file__).resolve().parent;R=E.parents[1];F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
B='/home/dombarker/project-offloads/codex-cx-slice-d-entry-20261105';H='dombarker@100.108.41.90'
C='crates/aspis-r1-cost-probe/src/'
files={};frozen={};binary={}
for n in subprocess.check_output(['git','ls-tree','-r','--name-only',F,'crates','programs'],text=True).splitlines()+['Cargo.lock','Cargo.toml']:
 b=subprocess.check_output(['git','show',F+':'+n]);frozen[n]=hashlib.sha256(b).hexdigest()
 try:files[n]=b.decode()
 except UnicodeDecodeError:binary[n]=base64.b64encode(b).decode()
base=dict(files)
# Own harness modules are installed in a later stage.
for name in ['NGL_reference','NGL_transport','NGL_verifier','NGL_compact','NGL_wire']:
 files[C+name+'.rs']='// Reserved prefix-owned input.\n'
inputs={n:s for n,s in files.items() if n not in base or s!=base[n]}
(E/'NGL_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n')
(E/'NGL_SOURCE_PINS.json').write_text(json.dumps({**frozen,**{n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()}},indent=1)+'\n')
(E/'NGL_FROZEN_SOURCE_PINS.json').write_text(json.dumps(frozen,indent=1)+'\n')
patch=[]
for n,s in inputs.items():patch+=difflib.unified_diff(base.get(n,'').splitlines(True),s.splitlines(True),fromfile='a/'+n if n in base else '/dev/null',tofile='b/'+n)
(E/'NGL_harness.patch').write_text(''.join(patch))
# Host tree is copied once from the retained frozen scratch. All frozen text is
# restored below; KMX files in that tree are verified by the strict run gate.
remote=f'''from pathlib import Path
import json,shutil,base64
b=Path({B!r});s=b/'NGL_src';assert not s.exists()
shutil.copytree('/home/dombarker/project-offloads/codex-cx-slice-d-define-20261104/NFQ_src',s,symlinks=False)
for n,t in json.loads({json.dumps(files)!r}).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
for n,t in json.loads({json.dumps(binary)!r}).items():(s/n).write_bytes(base64.b64decode(t))
(b/'NGL_SOURCE_PINS.json').write_text({(E/'NGL_SOURCE_PINS.json').read_text()!r})
print(json.dumps(dict(files={len(files)},frozen_revision={F!r})))
'''
# Fresh admission is mandatory before uploading source inputs.
for retry in range(11):
 a=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=f'''import subprocess,json,sys
from pathlib import Path
b=Path({B!r});p=b/'NGL_NATIVE_SETUP-admission.json'
with (b/'NGL_NATIVE_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''',text=True,capture_output=True)
 (E/'NGL_NATIVE_SETUP-admission.log').write_text(a.stdout+a.stderr)
 if a.returncode==0 and json.loads(a.stdout).get('allowed') is True:break
 if a.returncode==255 and retry<10:time.sleep(60);continue
 if (a.returncode==78 or json.loads(a.stdout).get('allowed') is False) and retry<10:time.sleep(180);continue
 raise RuntimeError('Admission failed; no upload')
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=remote,text=True,capture_output=True)
(E/'NGL_NATIVE_SETUP.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
print(r.stdout)
