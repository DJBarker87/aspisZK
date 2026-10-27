from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
rs=[json.loads(p.read_text()) for p in sorted(E.glob('J*/receipt.json'))]
ks=[json.loads(p.read_text()) for p in sorted(E.glob('K*/receipt.json'))]
assert len(rs)==100 and len(ks)==10
assert [r['attempt'] for r in rs]==list(range(42100,42200))
assert all(r['charged'] for r in rs)
assert all(str(r['swaps'])=='0' for r in rs)
allowed={'propext','Classical.choice','Quot.sound'}
manifest=json.loads((E/'AUDIT-MANIFEST.json').read_text());final={}
for r in rs:
 if r['exit']==0:final[(r['module'],r['source_sha256'])]=r
for p in L.glob('PV_Inv_*.lean'):
 h=hashlib.sha256(p.read_bytes()).hexdigest();assert ('R1Z/'+p.stem,h) in final,p
for r in rs:
 if r['exit']==0:
  for a in r['axioms']:
   if '[' in a:assert set(a.split('[',1)[1].rstrip(']').replace(' ','').split(','))<=allowed,a
for r in rs[-3:]:assert r['exit']==0 and 'Audit' in r['module']
axioms={}
for r in rs[-3:]:
 for a in r['axioms']:axioms[a.split("'")[1]]=a
for m in manifest:
 for d in m['declarations']:assert d in axioms,d
(E/'AXIOMS.md').write_text('# Final focused axioms audit\n\n'+ '\n'.join('- '+axioms[n] for n in sorted(axioms))+'\n')
rows=['# Receipts','', '| Attempt | Target | Exit | Wall | Peak RSS KiB | Swap |','|---|---|---:|---|---:|---:|']
for r in rs:rows.append(f"| [J{r['attempt']}](J{r['attempt']}/receipt.json) | {r['module']} | {r['exit']} | {r['wall']} | {r['peak_rss_kib']} | {r['swaps']} |")
for n,r in enumerate(ks,1):rows.append(f"| [K{n:02}](K{n:02}/receipt.json) | {r['target']} | {r['exit']} | {r['wall']} | {r['peak_rss_kib']} | {r['swaps']} |")
(E/'INDEX.md').write_text('\n'.join(rows)+'\n')
s=dict(lean_attempts=len(rs),lean_successes=sum(r['exit']==0 for r in rs),kani_runs=len(ks),kani_passes=sum(r['exit']==0 for r in ks),source_modules=len(manifest),audit_modules=3,audited_declarations=len({d for m in manifest for d in m['declarations']}),max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in rs),all_lean_swap_zero=True,refusals=0,kani_cli_rejections=sum(r['exit']==2 for r in ks),native_counterexample=False,row='V380-inversion',row_status='OPEN',premises_removed=0,target='not yet established',last_audit=rs[-1])
(E/'SUMMARY.json').write_text(json.dumps(s,indent=2)+'\n');print(json.dumps({k:v for k,v in s.items() if k!='last_audit'},indent=2))
(E/'HISTORY.txt').write_text(subprocess.check_output(['git','log','--oneline','9c4bfcc830c09f8d85fd1ed7996f8d9dcf059c84..HEAD'],cwd=R,text=True))
