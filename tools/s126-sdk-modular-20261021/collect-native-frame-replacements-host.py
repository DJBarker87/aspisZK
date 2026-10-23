#!/usr/bin/env python3
"""Retain failed focused frame replacements; neither carries proof credit."""
from pathlib import Path
import json,hashlib,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-native-frame-replacements-export-v1';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_text())
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
rows={}
for version in ['success-fixed-input-pair-v1','native-write-frame-v1']:
 tag='sdk-native-'+version.removeprefix('native-') if version.startswith('native-') else 'sdk-native-'+version
 P=H/('sdk-shared-prefix-'+version);i=load(H/(tag+'-input.json'));r=load(H/'receipts'/tag/'receipt.json');assert r['exit_status']!=0
 for rel in ['src/lib.rs','src/sdk_live_models.rs','Cargo.toml','Cargo.lock','source-cut.json']:
  if (P/rel).exists():copy(P/rel,Path('sources')/version/rel)
 for name in [tag,'sdk-shared-prefix-codegen-'+version]:
  for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:
   p=H/(name+suffix)
   if p.exists():copy(p,name+suffix)
  for p in (H/'receipts'/name).iterdir():
   if p.suffix in ['.json','.log']:copy(p,Path('receipts')/name/p.name)
 for p in (H/tag).iterdir():
  if p.is_file() and p.suffix in ['.json','.log','.c','.py']:copy(p,Path('cases')/version/p.name)
 cg=load(H/('sdk-shared-prefix-codegen-'+version+'-input.json'))
 for package,pin in cg['local_dependency_source_pins'].items():
  for rel,d in pin['files'].items():assert sha(H/'sdk-native-first-pair-export-v1/dependencies'/package/rel)==d
 rows[tag]=dict(accepted=False,version=version,source_sha256=sha(P/'src/lib.rs'),receipt=r)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=rows,dependency_evidence='../sdk-native-first-pair/dependencies',scope='Two source-changed focused replacements of the original-input-frame obligation. Coordinate-value strengthening and original native whole-write-footprint enforcement both stalled at SSA conversion and timed out under unchanged6G/8G/Swap0 caps. No proof credit and no counterexample inferred. Existing complete unseeded successful pair remains accepted separately.',next='Compose checked per-step SDK, copy and destructor footprints with actual source call-site instances; do not rerun these unchanged or raise caps.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file() and p.name!='manifest.json'}),indent=2)+'\n');print(O)
