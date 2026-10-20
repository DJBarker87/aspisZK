#!/usr/bin/env python3
"""Collect existing receipts only. Does not launch or retry any gate."""
import ast,hashlib,json,re,subprocess
from pathlib import Path
D=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
R='/home/dombarker/project-offloads/codex-cx-prover-commit2-20261020'
T='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
rows=[]
for p in sorted(D.glob('*/receipt.json')):
 r=json.loads(p.read_text());rows.append(dict(kind='extraction-or-runtime',attempt=p.parent.name,**r))
for a in range(8100,8400):
 p=D/'lean'/str(a)
 if not p.exists():continue
 meta=json.loads((p/'meta.json').read_text())
 out=(p/'out.log').read_text();tm=(p/'time.log').read_text()
 def n(label):
  m=re.search(re.escape(label)+r':\s*(\d+)',tm);return int(m[1]) if m else None
 wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.*)',tm)
 exits=re.findall(r'^exit=(\d+)',out,re.M)
 rows.append(dict(kind='lean',**meta,exit_status=int(exits[-1]) if exits else None,wall=wall[1] if wall else None,peak_rss_kib=n('Maximum resident set size (kbytes)'),swaps=n('Swaps'),axioms=[x for x in out.splitlines() if 'depends on axioms' in x],errors=[x for x in out.splitlines() if 'error' in x],source_revision='f2a598c6a',environment='J'))
for p in D.glob('*.py'):ast.parse(p.read_text())
(D/'attempts.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in rows))
artifacts={str(p.relative_to(D)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in sorted(D.rglob('*')) if p.is_file() and p.name!='manifest.json'}
(D/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',branch='codex/cx-prover-commit2-20261020',source_revision='f2a598c6a',frozen_verifier='b2727acd3',attempts=rows,artifacts=artifacts),indent=2)+'\n')
print(f'Collected {len(rows)} existing receipts.')
