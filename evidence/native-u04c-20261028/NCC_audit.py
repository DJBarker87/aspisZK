"""Evidence-only audit; never launches a prover."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
rows=[]
for p in sorted(E.glob('NCC_K*/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];s=(p.parent/'stdout.log').read_text();g=json.loads((E/(a+'-graph.json')).read_text())
 limits=r['limits'];assert limits['memory.high']=='6442450944' and limits['memory.max']=='8589934592' and limits['memory.swap.max']=='0' and limits['pids.max']=='64'
 assert g['graph_matches_frozen'] and g['lock_unchanged'];assert g['lock_before_sha256']==g['lock_after_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert r['source_hashes']['NBU_KMX_copy_stubs.patch']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 assert r['source_hashes']['NBU_src/KMX_stubs.rs']==r['source_hashes']['NBU_src/crates/aspis-statement/src/KMX_stubs.rs']=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
 start=s.find('Checking harness');tail=s[start:] if start>=0 else s[-1500:]
 if r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in tail:status='PASS'
 elif 'unwinding assertion' in tail:status='UNWIND'
 elif r['exit_status']==1 and 'VERIFICATION:- FAILED' in tail and 'Failed Checks:' in tail:status='COUNTEREXAMPLE'
 elif 'TIMEOUT' in s.upper() or 'TIMED OUT' in s.upper() or r['exit_status']==124:status='TIMEOUT'
 else:status='ERROR'
 cmd=r['command']
 for line in s.splitlines():
  if line.startswith('{'):
   try:x=json.loads(line)
   except json.JSONDecodeError:continue
   if 'kani_command' in x:cmd=x['kani_command'];break
 cmd=cmd[:];cmd[cmd.index('--harness')+1]='<target>'
 row=dict(attempt=a,module=r['module'],status=status,exit=r['exit_status'],wall=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],revision=r['source_revision'],limits=limits,command=cmd,env=r['env'],source_hashes=r['source_hashes'],diagnostic=tail[-1800:])
 rows.append(row)
pairs=[]
for i,row in enumerate(rows):
 if not row['module'].endswith('_negative'):continue
 positive=next((x for x in rows if x['module']==row['module'].removesuffix('_negative')),None)
 if positive is None:continue
 same=all(positive[k]==row[k] for k in ['command','env','limits'])
 keys=['NBU_src/crates/aspis-statement/src/pool_v1/NCC_slots.rs','NBU_src/crates/aspis-statement/src/pool_v1/verifier_registry.rs','NBU_src/KMX_stubs.rs','NBU_src/Cargo.lock']
 same=same and all(positive['source_hashes'][k]==row['source_hashes'][k] for k in keys)
 intended=row['status']=='COUNTEREXAMPLE' and 'unwind' not in row['diagnostic'].lower() and 'overflow' not in row['diagnostic'].lower()
 pairs.append(dict(positive=positive['attempt'],negative=row['attempt'],same_configuration=same,controlled=positive['status']=='PASS' and intended and same))
(E/'NCC_AUDIT.json').write_text(json.dumps(dict(kani_used=len(rows),lean_used=len(list(E.glob('NCC_L*/receipt.json'))),rows=rows,pairs=pairs,all_pairs_controlled=all(x['controlled'] for x in pairs),all_pairs_with_passing_positive_controlled=all(x['controlled'] for x in pairs if next(r for r in rows if r['attempt']==x['positive'])['status']=='PASS'),excluded_nonpassing_pairs=[x for x in pairs if next(r for r in rows if r['attempt']==x['positive'])['status']!='PASS']),indent=2)+'\n')
print(json.dumps(dict(kani_used=len(rows),statuses={k:sum(r['status']==k for r in rows) for k in ['PASS','COUNTEREXAMPLE','UNWIND','TIMEOUT','ERROR']},controlled_pairs=sum(p['controlled'] for p in pairs))))
