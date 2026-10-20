#!/usr/bin/env python3
"""Validate/summarize existing receipts. Never launches a build or retries it."""
import ast,hashlib,json,re,subprocess
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
P=ROOT/'docs/research/v8-r0-zk-20261009/lean'
base='f2a598c6a'
release=json.loads((D/'source-release.json').read_text()) if (D/'source-release.json').exists() else {}
host=json.loads((D/'host-artifact-pins.json').read_text())
llbc={r['path']:r for r in host['llbc']}
rows=[]
for p in sorted(D.glob('*/receipt.json')):
 r=json.loads(p.read_text());name=p.parent.name
 kind='source-extraction' if name.endswith(('-charon','-aeneas')) else ('kani' if 'kani' in name else 'rust-gate')
 row=dict(kind=kind,attempt=name,source_revision_base=base,**r)
 for arg in r['command']:
  if isinstance(arg,str) and arg.endswith('.llbc') and arg in llbc:row['llbc']=llbc[arg]
 q=D/(name+'-source-pins.json')
 if q.exists():row['source_pins']=q.name
 if name=='builder-carried-charon' or name=='builder-carried-aeneas':row['excluded']='harness manifest accidentally selected original source; corrected under builder-carried-fixed'
 rows.append(row)
accepted={}
for a in range(8100,8400):
 p=D/'lean'/str(a)
 if not (p/'meta.json').exists():continue
 meta=json.loads((p/'meta.json').read_text())
 if not (p/'out.log').exists():
  rows.append(dict(kind='launch-control',**meta,status='no compiler output/time receipt; reservation, dependency preflight or unchanged-direct-fingerprint refusal'))
  continue
 out=(p/'out.log').read_text();tm=(p/'time.log').read_text()
 def n(label):
  m=re.search(re.escape(label)+r':\s*(\d+)',tm);return int(m[1]) if m else None
 wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.*)',tm)
 exits=re.findall(r'^exit=(\d+)',out,re.M)
 status=int(exits[-1]) if exits else None
 axioms=[x for x in out.splitlines() if 'depends on axioms' in x]
 row=dict(kind='lean',**meta,exit_status=status,wall=wall[1] if wall else None,peak_rss_kib=n('Maximum resident set size (kbytes)'),swaps=n('Swaps'),axioms=axioms,errors=[x for x in out.splitlines() if ': error' in x],source_revision_base=base,environment='J')
 current=P/meta['module']
 matches=current.exists() and hashlib.sha256(current.read_bytes()).hexdigest()==meta['source_sha256']
 row['matches_current_source']=matches
 if status==0:
  assert all(set(re.search(r'\[(.*)\]',x)[1].split(', '))<= {'propext','Classical.choice','Quot.sound',''} for x in axioms),(a,axioms)
  if matches:accepted[meta['module']]=row
 rows.append(row)
for p in D.glob('*.py'):ast.parse(p.read_text())
# This is the published-source inventory, not a claim that draft sources are current.
source_pins=[]
for pattern in ['AspisR1ProverCommit/*.lean','AspisR1ProverStreams/*.lean','AspisR1ProverLeaf/*.lean','R1Z/ProverCommit*.lean']:
 for p in sorted(P.glob(pattern)):
  rel=str(p.relative_to(ROOT));sha=hashlib.sha256(p.read_bytes()).hexdigest()
  assert str(p.relative_to(P)) in accepted,rel
  if release.get('code_revision'):
   data=subprocess.check_output(['git','show',release['code_revision']+':'+rel])
   assert hashlib.sha256(data).hexdigest()==sha,rel
  source_pins.append(dict(path=rel,sha256=sha,bytes=p.stat().st_size))
(D/'source-inventory.json').write_text(json.dumps(source_pins,indent=2)+'\n')
(D/'attempts.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in rows))
(D/'accepted.json').write_text(json.dumps(accepted,indent=2)+'\n')
artifacts={str(p.relative_to(D)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in sorted(D.rglob('*')) if p.is_file() and p.name!='manifest.json'}
manifest=dict(schema='focused-extractor-proof-packet-v1',branch='codex/cx-prover-commit2-20261020',source_revision_base=base,source_release=release,frozen_verifier='b2727acd3',status='partial-source-facts; blocked on whole-builder/reference',discharged_checklist_rows=[],new_theorems=26,environment='J',attempt_range=[8100,8399],accepted_modules=accepted,attempts=rows,artifacts=artifacts)
(D/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'Validated {len(accepted)} current modules; collected {len(rows)} receipts/control records; no builds launched.')
