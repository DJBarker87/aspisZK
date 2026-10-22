#!/usr/bin/env python3
"""Validate only the new identity-bearing caller closure; no Lean replay."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
accepted={'S2SdkFixedInputCallerV1':('s2-sdk-fixed-input-caller-v10',3),
 'S126SdkFixedInputCurrentV1':('s126-sdk-fixed-input-current-v1',2),
 'S126SdkFixedInputExportV1':('s126-sdk-fixed-input-export-v2',4)}
manifest=read(E/'accepted-targets.json');pins=read(E/'focused-import-pins.json')
assert set(pins['targets'])==set(accepted)
modules={m['name']:m for m in pins['modules']};assert len(modules)==len(pins['modules'])
results=[]
for name,(attempt,count) in accepted.items():
 row=manifest['targets'][name];assert row['receipt']==attempt+'/receipt.json'
 d=E/attempt;r=read(d/'receipt.json');source=S/(name+'.lean')
 assert r['source_sha256']==sha(source)==sha(d/'source.lean')==row['source_sha256']
 assert r['exit_status']==0 and r['swaps']==0
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert len(r['print_axioms'])==count
 assert all(re.search(r'depends on axioms:\s*\[propext,\s*Classical.choice,\s*Quot.sound\]',a) for a in r['print_axioms'])
 assert not re.search(r'\bsorry\b|\bnative_decide\b|^axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)',source.read_text(),re.M)
 assert r['object_sha256']==pins['targets'][name]['object_sha256']
 for dep in r['direct_imports'].values():
  selected=[m for m in pins['modules'] if m['path']==dep['path']]
  assert len(selected)==1 and selected[0]['sha256']==dep['sha256']
 for imported in pins['targets'][name]['modules']:
  m=modules[imported]
  assert set(m['imports'])<=set(pins['targets'][name]['modules'])
 results.append(dict(target=name,exit_status=0,wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],swaps=0,print_axioms=r['print_axioms']))
for path in [E/a for a,_ in accepted.values()]:
 assert all(p.suffix not in ['.olean','.o','.a','.so','.dylib','.llbc','.bc'] for p in path.rglob('*') if p.is_file())
print(json.dumps(dict(schema='focused-extractor-proof-packet-v1',accepted=results,import_modules=len(modules),qualification='Complete installed reference success now derives original initial account0/account1 byte identities, actual decoder/current first, exact full proof/suffix lengths and contents. No extra caller premise. Native SDK successful continuation/heap embedding, TX2 retention, lead interface fields, original S1 Prepared correspondence, full R22 and release replay remain open.'),indent=2))
