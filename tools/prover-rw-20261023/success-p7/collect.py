"""Read-only proof/evidence validation; no builds or infrastructure changes."""
from pathlib import Path
import hashlib,json,re,subprocess
r=Path(__file__).resolve().parents[3]
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p7'
rows=[]
for p in sorted(e.glob('*-input.json')):
 x=json.loads(p.read_text());a=x['attempt']
 assert hashlib.sha256((e/f'{a}.lean.txt').read_bytes()).hexdigest()==x['source_sha256']
 o=(e/f'out-{a}.log').read_text();t=(e/f'time-{a}.log').read_text() if (e/f'time-{a}.log').exists() else ''
 m=re.search(r'^exit=(\d+)',o,re.M);status=int(m[1]) if m and t else None
 axioms=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",o)
 if status==0:
  assert 'sorryAx' not in o
  for line in axioms:
   if 'depends on axioms:' in line:assert set(n.strip() for n in line.split('depends on axioms: [')[1].split(']')[0].split(','))<={'propext','Classical.choice','Quot.sound'}
 x.update(exit_status=status,time_log=t,print_axioms=axioms,errors=[l for l in o.splitlines() if 'error:' in l],command=f"sh {x['launcher']} {a} {x['module']} J 7000 7 {x['deps_fingerprint']}",scope='Focused cached source check, no release replay')
 (e/f'{a}-receipt.json').write_text(json.dumps(x,indent=2)+'\n')
 rows.append(dict(attempt=a,module=x['module'],exit=status,wall=re.findall(r'Elapsed .*: (.*)',t),peak_rss_kib=re.findall(r'Maximum resident set size \(kbytes\): (.*)',t),swaps=re.findall(r'Swaps: (.*)',t),axiom_reports=len(axioms)))
native=[]
for p in sorted((e/'translation').glob('*/receipt.json')):
 x=json.loads(p.read_text())
 native.append(dict(attempt=x['attempt'],kind='Kani' if 'kani' in x['target'] else 'extraction',command=x['target'],exit=x['exit_status'],wall=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],cgroup_memory_peak_bytes=x['cgroup_memory_peak_bytes'],source_revision_label=x['source_revision'],scope='Exact source hashes pin inputs; historical host revision label is not this branch revision'))
result=dict(attempts=rows,native=native,lean_compiles=sum(x['exit'] is not None for x in rows),lean_passes=sum(x['exit']==0 for x in rows),kani_runs=sum(x['kind']=='Kani' for x in native),lean_budget=100,kani_budget=15,root_premises_removed=0,target_established=False)
(e/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
print({k:result[k] for k in ['lean_compiles','lean_passes','kani_runs','root_premises_removed']})
