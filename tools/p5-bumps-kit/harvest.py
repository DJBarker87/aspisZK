#!/usr/bin/env python3
import json,subprocess,hashlib
from pathlib import Path
from inventory import ROOT,OUT
HOST='dombarker@100.108.41.90';BASE='/home/dombarker/project-offloads/codex-cx-p5-bumps-20261021'
for phase,sub in [('phase2','')]+[(f'phase{i}',f'/phase{i}') for i in range(3,13)]:
 dest=OUT/'kani'/phase;dest.mkdir(parents=True,exist_ok=True)
 subprocess.run(['rsync','-a',HOST+':'+BASE+sub+'/receipts/',str(dest)+'/' ],check=True)
 snapshot=OUT/'source-contexts'/phase;snapshot.mkdir(parents=True,exist_ok=True)
 for f in ['lib.rs','source-pins.json','Cargo.toml']:
  subprocess.run(['rsync','-a',HOST+':'+BASE+sub+'/generated/'+f,str(snapshot/f)],check=True)
rows=[]
for p in sorted((OUT/'kani').glob('*/**/receipt.json')):
 r=json.loads(p.read_text());r['receipt_path']=str(p.relative_to(OUT));rows.append(r)
(OUT/'kani-manifest.json').write_text(json.dumps(dict(schema='p5-kani-manifest-v1',attempts=rows),indent=2)+'\n')
print(json.dumps(dict(attempts=len(rows),success=sum(r['verification_success'] for r in rows),failures=[r['attempt'] for r in rows if not r['verification_success']]),indent=2))
