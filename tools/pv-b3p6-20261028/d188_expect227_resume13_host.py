"""Freeze new executable Lean observations and their exact successful sources."""
from pathlib import Path
import json,hashlib
from run import H
out=[];evidence=[]
for i in range(66656,66660):
 p=H/f'lean-{i}/receipt/stdout.log'
 for line in p.read_text().splitlines():
  if not line.startswith('"'):continue
  label,values=json.loads(line).split('=',1);name,seed=label.split(':');out.append(dict(function=name,seed=int(seed),limbs=json.loads(values)))
 sub=json.loads((H/f'lean-{i}/submission.json').read_text());assert json.loads((H/f'lean-{i}/receipt/receipt.json').read_text())['exit_status']==0
 evidence.append(dict(attempt=i,source_sha256=sub['source_sha256'],stdout_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
assert len(out)==16
(H/'d18813-expected.json').write_text(json.dumps(out,indent=2)+'\n');(H/'d18813-expectation-chain.json').write_text(json.dumps(evidence,indent=2)+'\n')
