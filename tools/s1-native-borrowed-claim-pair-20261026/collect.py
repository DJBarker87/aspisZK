#!/usr/bin/env python3
"""Collect exact source-only current, predecessor and extraction evidence."""
from pathlib import Path
import hashlib,json,tarfile,subprocess
R=Path(__file__).resolve().parents[2];D=Path(__file__).resolve().parent
B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021'
O=E/'s1-native-borrowed-claim-profile-terminal-v1';O.mkdir()
def unpack(archive,destination):
 with tarfile.open(archive)as files:
  for member in files.getmembers():
   assert member.isfile()and not Path(member.name).is_absolute()and'..'not in Path(member.name).parts
   p=destination/member.name;p.parent.mkdir(parents=True,exist_ok=True)
   p.write_bytes(files.extractfile(member).read())
unpack('/tmp/s126-borrowed-claim-profile-terminal-20261026.tar.gz',O/'native')
unpack('/tmp/s126-claim-zero-copy-source-20261026.tar.gz',O/'extraction')
report=subprocess.check_output(['python3',str(D/'reuse.py')],cwd=R)
(O/'historical-reference-reuse.json').write_bytes(report)
old=E/'s1-native-borrowed-helper-20261024/historical-generated/AspisS1OwnedNestedClaim'
new=O/'extraction/generated/AspisS1OwnedNestedClaim'
import re
rows={}
for name in ['Types.lean','Funs.lean']:
 left=(old/name).read_text();right=(new/name).read_text()
 assert re.sub(r'/--[\s\S]*?-/', '',left)==re.sub(r'/--[\s\S]*?-/', '',right)
 rows[name]={'historical_sha256':hashlib.sha256((old/name).read_bytes()).hexdigest(),
             'zero_copy_sha256':hashlib.sha256((new/name).read_bytes()).hexdigest(),
             'exact_non_doc_bytes_equal':True}
for raw in (O/'extraction/generated').rglob('*.lean'):
 raw.rename(raw.with_suffix('.lean.txt'))
(O/'zero-copy-model-reuse.json').write_text(json.dumps(rows,indent=2)+'\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(O/'manifest.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1',
 'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'files':{str(p.relative_to(O)):sha(p)for p in sorted(O.rglob('*'))if p.is_file()},
 'native_whole_original_reference_paired_proof':False,
 'native_reference_characteristic_profile_all_cases':False,
 'accepted_reference_partitions':[0,1,2,3,4,6],
 'remaining_reference_partitions':[5],
 'actual_leaf_installation_proved':False,'whole_s1_closed':False,'whole_s6_closed':False,
 'qualification':'One-pass reference profile compared with prior checked original caller profile. Five common normal-return leaf interpretations retained; full trace/frame/state checks, complete native carriers, same emitted Lean program. No actual SDK/runtime/extraction/release join is inferred from this evidence inventory.'},indent=2)+'\n')
print(str(O))
