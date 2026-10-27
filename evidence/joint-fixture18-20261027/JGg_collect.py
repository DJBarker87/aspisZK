"""Collect exact receipts; never infer success from an object file's presence."""
from pathlib import Path
import json,re,hashlib
P=Path(__file__).resolve().parent;R=P.parents[1]
rs=[json.loads(p.read_text()) for p in sorted(P.glob('JGg18_*/receipt.json'))]
green={};failed=[]
for r in rs:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0'
 if r['exit_status']==0:
  for a in r['print_axioms']:
   assert 'sorryAx' not in a
   if '[' in a:assert set(re.search(r'\[([^]]*)\]',a)[1].split(', ')) <= {'propext','Classical.choice','Quot.sound'}
  for n,h in r['source_hashes'].items():green[n]={'source_hash':h,'attempt':r['attempt'],'axioms':r['print_axioms']}
 else:failed.append({'attempt':r['attempt'],'source_hashes':r['source_hashes'],'exit':r['exit_status'],'diagnostics':str(P/r['attempt']/'stdout.log')})
validated=[];pending=[]
for f in sorted((R/'lean').glob('JGg_*.lean')):
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',f.read_text()),f
 sha=hashlib.sha256(f.read_bytes()).hexdigest()
 if f.name in green and green[f.name]['source_hash']==sha:validated.append({'source':str(f.relative_to(R)),**green[f.name]})
 else:pending.append(str(f.relative_to(R)))
(P/'JGg_VALIDATION.json').write_text(json.dumps(validated,indent=2)+'\n')
(P/'JGg_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in rs))
(P/'JGg_FAILURES.json').write_text(json.dumps(failed,indent=2)+'\n')
s={'charged_lean_attempts':len(rs),'kani_runs':0,'accepted':sum(r['exit_status']==0 for r in rs),'rejected':len(failed),'validated_modules':len(validated),'pending_modules':pending,'total_wall_seconds':sum(r['wall_seconds'] for r in rs),'maximum_reported_peak_rss_kib':max(int(r['peak_rss_kib']) for r in rs),'swap':0,'new_hash_blocks':0,'reused_hash_blocks':90,'scope':'focused coherent pinned cache; no release or package replay'}
(P/'JGg_SUMMARY.json').write_text(json.dumps(s,indent=2)+'\n');print(json.dumps(s,indent=2))
