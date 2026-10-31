from NEF_host import *
import subprocess,hashlib,difflib
admit('NEF_PREPARE001')
r=py('''from pathlib import Path
import shutil
b=Path('/home/dombarker/project-offloads/codex-cx-slice-q-fnptr-20261029')
s=Path('/home/dombarker/project-offloads/codex-cx-kani-diag3-20261028/KNC_src')
if not (b/'NEF_src').exists():shutil.copytree(s,b/'NEF_src')
(b/'NEF_tmp').mkdir(exist_ok=True)
''');assert r.returncode==0,r.stderr
pins=json.loads((E/'NEF_SOURCE_PINS.json').read_text())
files={n:subprocess.check_output(['git','show',pins['frozen_revision']+':'+n],text=True) for n in pins['files']}
# Preserve known working research workspace manifest (three inactive tools excluded).
files.pop('Cargo.toml')
# Exact historical reproducer retained under its original names for diagnostics only.
files['crates/aspis-r1-cost-probe/src/candidate.rs']+='\n#[cfg(kani)]\nmod NBZ_native;\n#[cfg(kani)]\nmod NEF_native;\n'
files['crates/aspis-r1-cost-probe/src/NBZ_native.rs']=(E.parent/'kani-diag3-20261028/KNC_MINIMAL.rs.txt').read_text().replace('KNC_native','NBZ_native')
files['crates/aspis-r1-cost-probe/src/NEF_native.rs']='''use super::*;
#[kani::proof]
fn NEF_none_control() { assert!(None::<fn(Phase)>.is_none()); }
'''
r=py(f'''from pathlib import Path
import json,hashlib
b=Path({B!r})/'NEF_src'
files=json.loads({json.dumps(files)!r})
for n,t in files.items():p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
print(json.dumps({{n:hashlib.sha256((b/n).read_bytes()).hexdigest() for n in files}}))
''');assert r.returncode==0,r.stderr
(E/'NEF_SCRATCH_PINS.json').write_text(r.stdout)
patch=[]
for n,t in files.items():
 try:old=subprocess.check_output(['git','show',pins['frozen_revision']+':'+n],stderr=subprocess.DEVNULL,text=True)
 except subprocess.CalledProcessError:old=''
 if old!=t:patch+=difflib.unified_diff(old.splitlines(True),t.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n)
(E/'NEF_native.patch').write_text(''.join(patch))
for n in ['NEA_gate.py','NEA_graph.py']:
 t=(E.parent/'slice-q-leaves-20261029'/n).read_text().replace('NEA','NEF')
 (E/n.replace('NEA','NEF')).write_text(t)
for n in ['NEF_gate.py','NEF_graph.py']:
 t=(E/n).read_text();r=py(f'from pathlib import Path;Path({(B+"/"+n)!r}).write_text({t!r})');assert r.returncode==0
