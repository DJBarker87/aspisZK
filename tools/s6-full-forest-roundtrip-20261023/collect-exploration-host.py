#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,tarfile
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'s6-full-forest-exploration-export-v1';O.mkdir(exist_ok=False)
def copy(p,q):q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
for suffix in ['all','unrolled','snapshot-unrolled']:
 P=H/f's6-full-forest-codec-{suffix}-v1';D=O/suffix
 for p in (P/'input').iterdir():
  if p.is_file() and p.suffix in ['.rs','.toml','.lock','.json']:copy(p,D/'input'/p.name)
 for n in ['frozen-statement-binding.json','opaque-children.json','backend-renaming.json','source-equivalence-binding.json','snapshot-loop-binding.json']:
  if (P/n).is_file():copy(P/n,D/n)
 # Original frozen dependencies are recoverable from the adopted git revision.
 # Retain complete modified Rust files for the extraction references.
 for rel in ['src/atomic_statement.rs','src/pool_v1/pair_tree_profile.rs']:
  p=P/'frozen-source/crates/aspis-statement'/rel
  if p.is_file():copy(p,D/'candidate-statement'/rel)
 llbc={}
 for n in ['Codec.llbc','Codec-renamed.llbc']:
  p=P/n;llbc[n]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
 (D/'llbc-pins.json').write_text(json.dumps(llbc,indent=2)+'\n')
 for phase in ['charon','aeneas-renamed']:
  tag=f's6-full-forest-codec-{suffix}-{phase}-v1'
  for p in (H/'receipts'/tag).iterdir():
   if p.is_file():copy(p,D/phase/p.name)
  for tail in ['input','admission']:copy(H/(tag+'-'+tail+'.json'),D/phase/(tail+'.json'))
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,qualification='EXCLUDED full-codec extraction attempts: original digest borrow, then original snapshot frontier borrow, then original afterstate frontier borrow. Charon passes; Aeneas rejects. No imported artifacts or closure. Original frozen sources linked by revision; complete modified reference files retained; LLBC hashes only for excluded attempts.'),indent=2)+'\n')
with tarfile.open(str(O)+'.tar.gz','w:gz') as t:
 for p in O.rglob('*'):
  if p.is_file():t.add(p,arcname=str(p.relative_to(O)))
print(json.dumps(dict(files=len(files),archive=str(O)+'.tar.gz')))
