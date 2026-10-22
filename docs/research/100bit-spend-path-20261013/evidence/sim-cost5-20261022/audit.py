"""Read-only source/receipt audit; no Lean regression or build is launched."""
from pathlib import Path
import hashlib,json,re,subprocess
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
ev=Path(__file__).resolve().parent
lean=repo/'docs/research/v8-r0-zk-20261009/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[]
for a in range(8805,8819):
 r=json.loads((ev/f'receipt-{a}.json').read_text())
 assert r['attempt']==a and 8800<=a<=8999
 assert sha(ev/f'source-{a}.lean.txt')==r['source_sha256']
 assert r['caps']==dict(lean_memory_mb=7000,MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64)
 assert r['dependencies_stable'] and r['swaps']==0
 for dep in r['dependencies']:
  assert sha(lean/f"{dep['module']}.lean")==dep['source_sha256']
 assert f"exit={r['exit']}" in (ev/f'out-{a}.log').read_text()
 assert r['source_revision'] and r['deps_fingerprint'] and r['target'] and r['wall'] and r['peak_rss_kib']
 receipts.append(r)
accepted={r['module']:r for r in receipts if r['exit']==0}
assert set(accepted)=={'R1Z/SimCostWide5','R1Z/SimCostCollect5','R1Z/SimCostFormula5','R1Z/SimCostRetry5','R1Z/SimCostPass5Audit'}
final=(ev/'out-8818.log').read_text()
allowed={'propext','Classical.choice','Quot.sound'}
axioms=re.findall(r"^'([^']+)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)",final,re.M)
assert len(axioms)==38
for name,line in axioms:
 if 'depends on axioms:' in line:
  assert {x.strip() for x in line.split('[',1)[1].split(']',1)[0].split(',')}<=allowed
new_theorems=[]
for mod,r in accepted.items():
 src=lean/f'{mod}.lean'; text=src.read_text()
 assert sha(src)==r['source_sha256']
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option (maxRecDepth|maxHeartbeats)',text,re.M)
 for name in re.findall(r'^theorem (\w+)',text,re.M):
  full=mod.replace('/','.')+'.'+name
  assert full in dict(axioms),full
  new_theorems.append(full)
assert len(new_theorems)==29
before=ev/'endpoint-before.lean.txt';after=ev/'endpoint-after.lean.txt'
assert before.read_bytes()==after.read_bytes() and (ev/'endpoint.diff').read_bytes()==b''
assert 'sim_preparation : SimCostIdeal.Preparation' in before.read_text()
changed=subprocess.check_output(['git','diff','--name-only','a2d45dab7'],text=True).splitlines()
assert not any(p.startswith(('crates/','programs/')) for p in changed)
assert not any(p.startswith('docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommit') for p in changed)
assert not any(p.suffix in {'.olean','.elf','.tar','.gz'} for p in ev.rglob('*') if p.is_file())
assert not any(p.stat().st_size>5_000_000 for p in ev.rglob('*.json'))
result=dict(status='pass',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 attempts=[dict(attempt=r['attempt'],module=r['module'],exit=r['exit'],wall=r['wall'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],source_sha256=r['source_sha256'],deps_fingerprint=r['deps_fingerprint']) for r in receipts],
 accepted_modules={m:dict(attempt=r['attempt'],sha256=r['source_sha256']) for m,r in accepted.items()},
 new_theorems=new_theorems,final_axiom_audits=axioms,peak_all_kib=max(r['peak_rss_kib'] for r in receipts),
 peak_accepted_kib=max(r['peak_rss_kib'] for r in receipts if r['exit']==0),
 endpoint_signature_sha256=sha(before),premises_removed=[],shipped_files_changed=[],large_json_files=[],
 scope='Focused cached assembly only; no complete frozen-manifest replay or full preparation closure')
(ev/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','final_axiom_audits','peak_all_kib','peak_accepted_kib','scope']},indent=2))
