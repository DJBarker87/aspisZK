"""Compare every scratch input with its frozen Git source or recorded overlay."""
from pathlib import Path
import subprocess,json,hashlib,re
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-pc-helpers1-20261110'
code=f'''from pathlib import Path
import json,hashlib
s=Path({B!r})/'PCB_src';print(json.dumps({{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file() and 'target' not in p.parts}}))'''
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
actual=json.loads(r.stdout);errors=[];rows=[]
for n,h in actual.items():
 if n.startswith('KMX_') or Path(n).name.startswith('PCB_'):continue
 rev='b936275465600469312d1f058cdc91ea2a11f3dc' if n.startswith('programs/aspis-pool/') else '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
 expected=hashlib.sha256(subprocess.check_output(['git','show',rev+':'+n])).hexdigest()
 overlays={k[len('PCB_src/'):]:v for task in json.loads((E/'PCB_TASKS.json').read_text()).values() for k,v in task.get('files',{}).items() if k.startswith('PCB_src/') and v.endswith('.rs.txt')}
 patched=n in overlays
 if not patched and h!=expected:errors.append(n)
 if patched:
  overlay=(E/overlays[n]).read_bytes();assert h==hashlib.sha256(overlay).hexdigest(),n
  frozen=subprocess.check_output(['git','show',rev+':'+n]).decode()
  def erase(text):
   text=re.sub(r'\n#\[cfg\((?:kani|any\(kani,\s*PCB_EXTRACT\))\)\]\n#\[path="PCB_[0-9]+\.rs"\]\nmod PCB_[0-9]+;\n','\n',text)
   text=re.sub(r'\n#\[cfg\(kani\)\]\nextern crate alloc;\n','\n',text)
   lines=[]
   for line in text.splitlines():
    v=line.strip()
    if v.startswith('#![cfg_attr(kani,feature(allocator_api))]'):continue
    if v.startswith('#[cfg_attr(kani,derive(kani::Arbitrary))]'):continue
    if v.startswith('#[cfg_attr(all(kani,'):continue
    if v.startswith('#[cfg_attr(kani,kani::ensures('):continue
    if v:lines.append(line.rstrip())
   return '\n'.join(lines)
  assert erase(overlay.decode())==erase(frozen),'default source differs beyond cfg proof overlays: '+n

 rows.append(dict(path=n,revision=rev,expected=expected,actual=h,cfg_kani_scratch_overlay=patched))
(E/'PCB_FROZEN_INPUTS.json').write_text(json.dumps(dict(rows=rows,errors=errors),indent=1)+'\n');assert not errors,errors
code=f'''from pathlib import Path
import json
b=Path({B!r});(b/'PCB_SOURCE_PINS.json').write_text({json.dumps(actual)!r})'''
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
print('PCB frozen scratch audit: '+str(len(rows))+' files, zero drift')
