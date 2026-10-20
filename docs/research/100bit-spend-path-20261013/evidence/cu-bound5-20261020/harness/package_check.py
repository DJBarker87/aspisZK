"""Final independent checks, resource receipts and retained-input inventory."""
import ast,hashlib,json,subprocess,sys
from pathlib import Path
H=Path(sys.argv[1]);read=lambda p:json.loads(p.read_text());checks={}
for p in (H/'harness').glob('*.py'):ast.parse(p.read_text(),filename=str(p))
for p in (H/'harness').glob('*.sh'):subprocess.run(['bash','-n',str(p)],check=True)
rs=[read(p) for p in (H/'receipts').glob('*/receipt.json')]
assert all(r['exit_status']==0 and r['swaps']==0 for r in rs)
assert all(r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'} for r in rs)
checks['completed_gate_receipts']=len(rs);checks['max_gate_peak_rss_kib']=max(r['peak_rss_kib'] for r in rs)
t=read(H/'trace-inventory.json');assert t and all(r['deleted'] and not (H/r['path']).exists() for r in t)
assert not list((H/'traces').rglob('*.regs')) and not list((H/'traces').rglob('*.insns'))
checks.update(deleted_trace_files=len(t),deleted_trace_bytes=sum(r['bytes'] for r in t),swaps=0)
# Task-generated keys stay on host; inventory names/hashes only, never contents.
inputs=[]
for root in [H/'harness',H/'src/tools/r1-cost-probe-sweep',H/'src/tools/r1-cost-probe-sweep-trace']:
 for p in sorted(root.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts:continue
  inputs.append(dict(path=str(p.relative_to(H)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(H/'harness-inputs.json').write_text(json.dumps(inputs,indent=1)+'\n')
keys=list((H/'sweep').rglob('*-keypair.json'))
assert len(keys)==2*read(H/'validation.json')['run_receipts']
checks['retained_keypair_files']=len(keys)
checks['key_deletions']=0
checks['canonical_caps']=read(H/'canonical-cap-check.json')
checks['target_revision']='2318acd430b8474de01e6117248442e3ab0b17b9'
checks['source_revision']='c16e59e77a8ee3249d61838b535a6a44ac918caf'
checks['print_axioms']='N/A: no Lean compilation'
(H/'package-check.json').write_text(json.dumps(checks,indent=1)+'\n');print(json.dumps(checks,indent=1))
