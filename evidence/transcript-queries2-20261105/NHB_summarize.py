from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
runs=[]
for p in sorted(E.glob('NHB_[LK][0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());raw=(p.parent/'stdout.log').read_text()
 if r['kind']=='kani':
  if 'timed out' in raw or 'CBMC failed' in raw:status='TOOL_LIMIT'
  elif r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in raw:status='PASS'
  elif re.search(r'\*\* 1 of \d+ failed',raw) and 'Failed Checks:' in raw and 'unwinding assertion' not in raw:status='ASSERTION_FAILED'
  else:status='OTHER_FAILURE'
 else:status='PASS' if r['exit_status']==0 else 'EXCLUDED_FAILURE'
 runs.append(dict(attempt=r['attempt'],kind=r['kind'],target=r['module'],status=status,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],cgroup_peak_bytes=r.get('cgroup_memory_peak_bytes'),swaps=r['swaps'],source_revision=r['source_revision'],source_hashes=r['source_hashes'],limits=r['limits'],print_axioms=r['print_axioms'],receipt=str(p.relative_to(E)),receipt_sha256=sha(p)))
counts={k:sum(r['kind']==k for r in runs) for k in ['kani','lean','link','audit']}
(E/'NHB_RESULTS.json').write_text(json.dumps(dict(runs=runs,counts=counts,root='TX1:168',composed_rows_added=0),indent=2)+'\n')
print(json.dumps(dict(counts=counts,native_pass=sum(r['kind']=='kani' and r['status']=='PASS' for r in runs),native_limits=sum(r['kind']=='kani' and r['status']=='TOOL_LIMIT' for r in runs))))
