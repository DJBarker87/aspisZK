"""Validate focused receipts, current theorem audit and unchanged endpoint."""
from pathlib import Path
import hashlib,json,re,subprocess
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
ev=Path(__file__).resolve().parent
lean=repo/'docs/research/v8-r0-zk-20261009/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(ev.glob('receipt-*.json'))]
known={}
for r in receipts:
 p=ev/f"source-{r['attempt']}.lean.txt"
 assert sha(p)==r['source_sha256']
 known.setdefault(r['module'],set()).add(r['source_sha256'])
for r in receipts:
 a=r['attempt']
 assert 8819<=a<=8999 and r['dependencies_stable'] and r['swaps']==0
 assert r['caps']==dict(lean_memory_mb=7000,MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64)
 assert all(r.get(k) is not None for k in ['target','wall','peak_rss_kib','source_revision','deps_fingerprint'])
 assert f"exit={r['exit']}" in (ev/f'out-{a}.log').read_text()
 for d in r['dependencies']:
  assert d['source_sha256']==sha(lean/f"{d['module']}.lean") or d['source_sha256'] in known.get(d['module'],set())
accepted={r['module']:r for r in receipts if r['exit']==0}
assert len(accepted)==6
axioms=re.findall(r"^'([^']+)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)",(ev/'out-8830.log').read_text(),re.M)
assert len(axioms)==24,len(axioms)
allowed={'propext','Classical.choice','Quot.sound'}
for _,a in axioms:
 if '[' in a:assert {x.strip() for x in a.split('[',1)[1].split(']',1)[0].split(',')}<=allowed
names=dict(axioms); new=[]
for mod,r in accepted.items():
 src=lean/f'{mod}.lean'
 assert sha(src)==r['source_sha256']
 s=src.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option (maxRecDepth|maxHeartbeats)',s,re.M)
 ns=re.search(r'^namespace (\S+)',s,re.M)
 for name in re.findall(r'^theorem (\w+)',s,re.M):
  full=ns.group(1)+'.'+name
  assert full in names,full
  new.append(full)
assert len(new)==21,len(new)
before=ev/'endpoint-before.lean.txt';after=ev/'endpoint-after.lean.txt'
assert before.read_bytes()==after.read_bytes() and (ev/'endpoint.diff').read_bytes()==b''
assert 'sim_preparation : SimCostIdeal.Preparation' in before.read_text()
changed=subprocess.check_output(['git','diff','--name-only','c8f6733d3'],text=True).splitlines()
assert not any(p.startswith(('crates/','programs/')) for p in changed)
assert not any(p.startswith('docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommit') for p in changed)
assert not any(p.suffix in {'.olean','.elf','.tar','.gz'} for p in ev.rglob('*') if p.is_file())
assert not any(p.stat().st_size>5_000_000 for p in ev.rglob('*.json'))
host=json.loads((ev/'host-hashes-and-range.json').read_text())
for mod,r in accepted.items():
 h=host['modules'][mod.split('/')[-1]]
 assert h['sources']['sha256']==r['source_sha256'] and h['objects']==r['object']
assert set(range(8800,8831)) <= set(host['used_attempts_8800_8999'])
result=dict(status='pass',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 attempts=[{k:r[k] for k in ['attempt','module','exit','wall','peak_rss_kib','swaps','source_revision','source_sha256','deps_fingerprint']} for r in receipts],
 accepted_modules={m:dict(attempt=r['attempt'],source_sha256=r['source_sha256'],object=r['object']) for m,r in accepted.items()},
 new_theorems=new,axioms=axioms,endpoint_signature_sha256=sha(before),premises_removed=[],
 shipped_files_changed=[],scope='Focused cached assembly. No full Preparation closure or frozen-manifest release replay.')
(ev/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='pass',new_theorems=len(new),axioms=len(axioms),scope=result['scope']),indent=2))
