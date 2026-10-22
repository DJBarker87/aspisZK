#!/usr/bin/env python3
"""Source-only accepted checkpoint-writer closure and exact reference-layer scope."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';D=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=load(E/'accepted-targets.json');pins=load(E/'checkpoint-writer-import-pins.json');accepted=[]
for name,count in [('S2SdkCheckpointWriterV1',2),('S2SdkSavedFirstV1',3),('S2SdkFixedSavedFirstV1',3),('S126SdkFixedSavedCurrentV1',2)]:
 row=manifest['targets'][name];r=load(E/row['receipt']);source=D/(name+'.lean');receiptDir=(E/row['receipt']).parent
 assert r['exit_status']==0 and r['swaps']==0 and len(r['print_axioms'])==count
 assert r['source_sha256']==sha(source)==sha(receiptDir/'source.lean')==pins['targets'][name]['source_sha256']
 assert r['object_sha256']==pins['targets'][name]['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert all('sorryAx' not in a and all(x.strip() in ['propext','Classical.choice','Quot.sound'] for x in a.split('[')[-1].rstrip(']').split(',')) for a in r['print_axioms'])
 assert not re.search(r'\bsorry\b|\bnative_decide\b|^\s*(?:axiom|opaque)\b',source.read_text(),re.M)
 assert 'error:' not in (receiptDir/'lean.log').read_text()
 for name_,owner in r['direct_imports'].items():
  selected=[x for x in pins['modules'] if x['name']==name_ and x['path']==owner['path']];assert len(selected)==1 and selected[0]['sha256']==owner['sha256']
 accepted.append(dict(target=name,receipt=row['receipt'],wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],swaps=r['swaps'],axioms_reports=count))
print(json.dumps(dict(accepted=accepted,qualification='Complete installed reference success is the sole enclosing premise; derives SAME original-input/source-current-first and saved original-account2-slot checkpoint. Native SDK runtime/heap and source child/gate/scan/oracle/TX2 transport remain. Focused compilation, not a coherent release rebuild.'),indent=2))
