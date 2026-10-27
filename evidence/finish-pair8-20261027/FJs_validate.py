"""Aggregate exact receipts and current source coverage; no compiler invocation."""
from pathlib import Path
import json,hashlib,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
receipts=[]
for p in sorted(P.glob('FJs_[0-9][0-9][0-9]/receipt.json')):
 j=json.loads(p.read_text());receipts.append(j)
 assert j['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},(p,j['limits'])
 assert int(j['swaps'])==0
 assert '-M7000' in j['command']
 assert not any(x in j['command'] for x in ['--run','native_decide'])
assert len(receipts)<=100
(P/'FJs_attempts.jsonl').write_text(''.join(json.dumps(j,sort_keys=True)+'\n' for j in receipts))
coverage=[]
for src in sorted((R/'lean').glob('FJs_*.lean')):
 sha=hashlib.sha256(src.read_bytes()).hexdigest()
 passing=[j for j in receipts if j['exit_status']==0 and j['source_hashes'].get(src.name)==sha]
 assert passing,('No passing current source receipt',src)
 j=passing[-1]
 assert not any('sorryAx' in a for a in j['print_axioms']),src
 coverage.append(dict(module=src.stem,sha256=sha,attempt=j['attempt'],axioms=j['print_axioms']))
for src in (R/'lean').glob('FJs_*.lean'):
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option (maxRecDepth|maxHeartbeats)',src.read_text(),re.M),src
changed=subprocess.check_output(['git','diff','--name-only','19626de7ff','--'],cwd=R,text=True).splitlines()
assert all(x.startswith('lean/FJs_') or x.startswith('evidence/finish-pair8-20261027/') for x in changed),changed
out=dict(attempts=len(receipts),lean_starts=len(receipts),kani_runs=0,passed=sum(j['exit_status']==0 for j in receipts),failed=sum(j['exit_status']!=0 for j in receipts),
 peak_rss_kib=max(int(j['peak_rss_kib']) for j in receipts),swaps=0,current_source_modules=len(coverage),coverage=coverage,
 source_revision_at_aggregation=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 source_tree_dirty=True,limits={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64,'lean':'-M7000'},
 full_package_replay=False,shipped_source_changes=False,elf_rebuild_triggered=False,
 inherited_elf_pins={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','Pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'})
(P/'FJs_validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='coverage'}))
