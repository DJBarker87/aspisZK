#!/usr/bin/env python3
"""Focused source-only iterator native/reference extraction evidence."""
from pathlib import Path
import hashlib,json,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-iterator-export';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,rel):
 q=O/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
def cut(s,name):
 a=s.index('pub fn '+name);b=s.index('{',a)+1;depth=1;i=b
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
sources={};pins=[]
for n in [1,2,3]:
 tag='sdk-iterator-reference-v'+str(n);p=H/tag
 for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json','charon-input.json','aeneas-input.json']:
  if (p/rel).is_file():copy(p/rel,Path(tag)/rel)
 sources[tag]=(p/'src/lib.rs').read_text()
 for phase in ['charon','aeneas']:
  for f in (H/'receipts'/(tag+'-'+phase)).glob('*'):
   if f.suffix in ['.json','.log']:copy(f,Path(tag)/'receipts'/phase/f.name)
  admission=H/(tag+'-'+phase+'-admission.json')
  if admission.exists():copy(admission,Path(tag)/admission.name)
 if n==2:
  for f in (p/'generated').rglob('*.lean'):copy(f,Path(tag)/(str(f.relative_to(p))+'.txt'))
 llbc=p/'Iterator.llbc'
 if llbc.exists():
  x=json.loads(llbc.read_text());pins.append(dict(tag=tag,sha256=sha(llbc),has_errors=x['has_errors']))
for n in [1,2,3]:
 tag='sdk-iterator-reference-join-v'+str(n)
 for f in (H/'receipts'/tag).glob('*'):
  if f.suffix in ['.json','.log']:copy(f,Path('native-receipts')/tag/f.name)
 for suffix in ['-input.json','-admission.json']:
  if (H/(tag+suffix)).exists():copy(H/(tag+suffix),Path('native-receipts')/(tag+suffix))
for f in (H/'target/kani/x86_64-unknown-linux-gnu/debug/.fingerprint').glob('*sdk-iterator*/*.json'):
 copy(f,Path('compiler-flags')/f.parent.name/f.name)
function_pins={}
for name in ['source_begin','source_next']:
 bodies=[cut(s,name) for s in sources.values()];assert len(set(bodies))==1
 function_pins[name]=dict(source=bodies[0],sha256=hashlib.sha256(bodies[0].encode()).hexdigest(),all_native_and_extracted_bodies_identical=True)
(O/'source-pins.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',protocol_freeze='b2727acd3abf79315d18b754a260f58f4b1c6326',extraction_parent_revision='9b6ba762d',functions=function_pins,llbc=pins,qualification='Native join v3 checks constructor plus one next step, every1768-byte value/cursor0..1768, full OwnedSdk rows and live AccountInfo RefMut. Exact bodies equal extraction v2; no unchanged extraction replay. Pointer-slot heap construction and complete shipped parent remain outside this leaf certificate.'),indent=2)+'\n')
for name in ['prepare-sdk-iterator-reference.py','extract-sdk-iterator-host.py','collect-sdk-iterator-host.py']:
 p=H/'kit'/name
 if p.is_file():copy(p,Path('runner')/name)
print('focused source-only SDK iterator export',O)
