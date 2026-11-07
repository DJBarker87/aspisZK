"""Classify complete multiline #print axioms replies; elaboration alone is no credit."""
from pathlib import Path
import json,re,hashlib
base=Path(__file__).resolve().parent
allowed={'propext','Classical.choice','Quot.sound'}
rows=[]
for receipt in sorted(base.glob('NNH_L*/receipt.json')):
 d=json.loads(receipt.read_text());log=receipt.parent/'stdout.log'
 text=log.read_text() if log.exists() else ''
 roots=[]
 for m in re.finditer(r"'([^']+)' (does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",text,re.S):
  axioms=[] if m[2].startswith('does not') else [x.strip() for x in m[3].split(',') if x.strip()]
  roots.append(dict(root=m[1],axioms=axioms,nonstandard=[x for x in axioms if x not in allowed]))
 rows.append(dict(attempt=d['attempt'],module=d.get('module'),exit_status=d['exit_status'],roots=roots,
  standard_prints=bool(roots) and all(not r['nonstandard'] for r in roots),stdout_sha256=hashlib.sha256(text.encode()).hexdigest()))
out=dict(allowed=sorted(allowed),no_row_credit=True,elaboration_is_not_admission=True,attempts=rows)
(base/'NNH_AXIOM_CLASSIFICATION.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(dict(scopes=len(rows),exit0_with_nonstandard=[x['attempt'] for x in rows if x['exit_status']==0 and any(r['nonstandard'] for r in x['roots'])])))
