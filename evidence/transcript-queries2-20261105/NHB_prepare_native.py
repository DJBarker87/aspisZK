from pathlib import Path
import subprocess,json,lzma,hashlib,difflib
E=Path(__file__).resolve().parent;P=E.parent/'transcript-queries-20261105'
B='/home/dombarker/project-offloads/codex-cx-transcript-queries2-20261105'
frozen=json.loads(lzma.decompress((P/'NGQ_FROZEN_INPUTS.json.xz').read_bytes()));files=dict(frozen)
patch=(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
for part in patch.split('diff --git ')[1:]:
 head,*ls=part.splitlines();name=head.split(' b/')[1];files[name]='\n'.join(l[1:] for l in ls if l.startswith('+') and not l.startswith('+++'))+'\n'
p='crates/aspis-core/src/lib.rs';files[p]=files[p].replace('#![no_std]','#![cfg_attr(kani, feature(allocator_api))]\n#![no_std]')+'\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod KMX_stubs;\n'
p='crates/aspis-core/src/r0_transcript.rs';files[p]+='\n#[cfg(kani)]\n#[path="NHB_harness.rs"]\nmod NHB_harness;\n'
files['crates/aspis-core/src/NHB_harness.rs']=(E/'NHB_contains.rs.txt').read_text()
(E/'NHB_HARNESSES.patch').write_text(''.join(''.join(difflib.unified_diff(frozen.get(p,'').splitlines(True),t.splitlines(True),fromfile='a/'+p,tofile='b/'+p)) for p,t in files.items() if frozen.get(p)!=t))
(E/'NHB_SOURCE_PINS.json').write_text(json.dumps({p:hashlib.sha256(t.encode()).hexdigest() for p,t in files.items()},indent=1)+'\n')
# Revalidate admission before upload, never infer permission from exit alone.
script=f'''from pathlib import Path
import subprocess,json,sys
b=Path({B!r});p=b/'NHB_NATIVE_SETUP.json'
with (b/'NHB_NATIVE_SETUP.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=script,text=True,capture_output=True)
(E/'NHB_NATIVE_SETUP.log').write_text(r.stdout+r.stderr);assert r.returncode==0 and json.loads(r.stdout).get('allowed') is True,(r.returncode,r.stdout)
script=f'''from pathlib import Path
import json
b=Path({B!r})/'NHB_src';files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
print(len(files))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=script,text=True,capture_output=True);assert r.returncode==0,r.stderr;print(r.stdout)
