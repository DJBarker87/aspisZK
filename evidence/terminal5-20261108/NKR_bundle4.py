from pathlib import Path
import subprocess,json,difflib,hashlib
E=Path(__file__).resolve().parent;P=E/'NKR_K056/sources';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
newmods=json.loads((E/'NKR_NATIVE_MODULES.json').read_text());oldmods=json.loads((P/'NKR_NATIVE_MODULES.json').read_text())
patch='';delta='';pins={};root='crates/aspis-statement/src/pool_v1/'
def diff(a,b,path):return ''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='a/'+path if a else '/dev/null',tofile='b/'+path))
def annotated(base,mods):return base+''.join('\n#[cfg(kani)]\n#[path="'+s+'.rs"]\nmod '+m+';\n'for s,m in mods)
for filename,mods in newmods.items():
 path=root+filename;base=subprocess.check_output(['git','show',rev+':'+path],text=True);old=annotated(base,oldmods[filename]);new=annotated(base,mods);patch+=diff(base,new,path);delta+=diff(old,new,path);pins[path]=hashlib.sha256(new.encode()).hexdigest()
 for stem,mod in mods:
  p=E/(stem+'.rs.txt');assert p.exists(),p;new=p.read_text();old=(P/p.name).read_text()if(P/p.name).exists()else'';path=root+stem+'.rs';patch+=diff('',new,path);delta+=diff(old,new,path);pins[path]=hashlib.sha256(new.encode()).hexdigest()
path='crates/aspis-statement/src/lib.rs';base=subprocess.check_output(['git','show',rev+':'+path],text=True);new='#![cfg_attr(kani,feature(allocator_api))]\n'+base;patch+=diff(base,new,path);pins[path]=hashlib.sha256(new.encode()).hexdigest()
(E/'NKR_native.patch').write_text(patch);(E/'NKR_UPDATE4.patch').write_text(delta);(E/'NKR_SOURCE_PINS.json').write_text(json.dumps(pins));print('Fourth native bundle/delta source pins complete')
