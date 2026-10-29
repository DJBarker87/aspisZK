#!/usr/bin/env python3
"""Prepare the lane's own scratch-only scalar contract patch."""
from pathlib import Path
import difflib,hashlib,json,subprocess
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-q-compose-20261029';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
n='crates/aspis-core/src/field.rs';old=subprocess.check_output(['git','show',F+':'+n],text=True)
new=old.replace('fn reduce_u64(x: u64) -> u32 {','#[cfg_attr(kani,kani::ensures(|r| NEB_reducer::reduce_post(x,*r)))]\nfn reduce_u64(x: u64) -> u32 {',1)
new=new.replace('    pub fn reduce_u64(value: u64) -> M31 {','    #[cfg_attr(kani,kani::ensures(|r| NEB_reducer::wrapper_post(value,*r)))]\n    pub fn reduce_u64(value: u64) -> M31 {',1)
new+='\n#[cfg(kani)] #[path="field/NEB_reducer.rs"] mod NEB_reducer;\n'
assert new!=old and new.count('NEB_reducer::reduce_post')==1 and new.count('NEB_reducer::wrapper_post')==1
files={n:new,'crates/aspis-core/src/field/NEB_reducer.rs':(E/'NEB_reducer.rs').read_text()}
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
extra='crates/aspis-core/src/field/NEB_reducer.rs';patch+=''.join(difflib.unified_diff([],files[extra].splitlines(True),fromfile='/dev/null',tofile='b/'+extra));(E/'NEB_reducer.patch').write_text(patch)
code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});s=b/'NEB_src'
for n,v in json.loads({json.dumps(files)!r}).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(v)
pins=json.loads((b/'NEB_SOURCE_PINS.json').read_text())
for n in json.loads({json.dumps(files)!r}):pins[n]=hashlib.sha256((s/n).read_bytes()).hexdigest()
(b/'NEB_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\\n')
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stdout+r.stderr
print(json.dumps(dict(patch_sha256=hashlib.sha256(patch.encode()).hexdigest(),frozen_revision=F,shipped_files_changed=0)))
