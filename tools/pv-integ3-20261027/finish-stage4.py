"""Reuse unchanged successful theorem evidence; never launches Lean."""
from pathlib import Path
import json,hashlib,subprocess,re
E=Path('evidence/pv-integ1-20261027/d298');audit=json.loads((E/'lean-source-assessment.json').read_text());assert not audit['recompile_required']
rows=[]
for name in audit['reused_op223_receipts']+audit['reused_batch_audits']:
 p=Path(name);r=json.loads(p.read_text());assert r.get('exit_status',r.get('exit'))==0
 axioms=r.get('print_axioms',r.get('axiom_output',[]));axioms=axioms.splitlines() if isinstance(axioms,str) else axioms
 for line in axioms:
  for found in re.findall(r'\[([^\]]*)\]',line):assert set(x.strip() for x in found.split(',') if x.strip())<= {'propext','Classical.choice','Quot.sound'},line
 rows.append(dict(receipt=name,receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),target=r['module'],source_revision=r['source_revision'],exit=0,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swap=r.get('swaps',r.get('swap')),print_axioms=axioms))
(E/'lean-reuse.json').write_text(json.dumps(dict(changed_imported_sources=[],decision='No fresh compile per task conditional rule; unchanged source/receipt reuse only',source_assessment='lean-source-assessment.json',lean_attempts=0,kani_attempts=0,used_ids=[],unused_env_j_range=[28000,28099],receipts=rows),indent=2)+'\n')
subprocess.run(['git','add','--',str(E/'lean-reuse.json'),'tools/pv-integ3-20261027/finish-stage4.py'],check=True)
subprocess.run(['git','commit','-m','Record unchanged op223 and batch source proof evidence for D298','--',str(E/'lean-reuse.json'),'tools/pv-integ3-20261027/finish-stage4.py'],check=True)
