"""Read-only focused compile receipts; never launches a build."""
from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parents[3]
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-resume'
rows=[]
for p in sorted(e.glob('*-input.json')):
 x=json.loads(p.read_text());a=x['attempt']
 assert hashlib.sha256((e/f'{a}.lean.txt').read_bytes()).hexdigest()==x['source_sha256']
 o=(e/f'out-{a}.log').read_text();t=(e/f'time-{a}.log').read_text() if (e/f'time-{a}.log').exists() else ''
 status=re.search(r'^exit=(\d+)',o,re.M);status=int(status[1]) if status and t else None
 axioms=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",o)
 if status==0:
  assert 'sorryAx' not in o
  for line in axioms:
   if 'depends on axioms:' in line: assert set(n.strip() for n in line.split('depends on axioms: [')[1].split(']')[0].split(','))<={'propext','Classical.choice','Quot.sound'}
 x.update(exit_status=status,time_log=t,print_axioms=axioms,errors=[l for l in o.splitlines() if 'error:' in l],command=f"sh {x['launcher']} {a} {x['module']} J 7000 7 {x['deps_fingerprint']}",scope='Focused proof only; no release replay or native association')
 if a==12416:
  x.update(source_revision='49bf51d3e9afab9691df3d2aacbba4905dda4a05',deps_argument_at_launch='',effective_launcher_deps_fingerprint='none',input_receipt_reconstruction='Initial input command used an absent local-script path; shell continued and launched once with empty fingerprint. Snapshot/dependency receipt reconstructed before changing any source/dependency; exact target/source retained. No rerun.',command=f"sh {x['launcher']} {a} {x['module']} J 7000 7 ''")
 if a==12467: x['pre_launch_note']='Fingerprint-read path typo stopped preparation before launcher; corrected path then launched once. No proof rerun.'
 if a==12485: x['pre_launch_note']='Local bounds-generator parse failure fixed before any input receipt or launcher invocation. One Lean launch.'
 (e/f'{a}-receipt.json').write_text(json.dumps(x,indent=2)+'\n')
 rows.append(dict(attempt=a,module=x['module'],exit=status,wall=re.findall(r'Elapsed .*: (.*)',t),peak_rss_kib=re.findall(r'Maximum resident set size \(kbytes\): (.*)',t),swaps=re.findall(r'Swaps: (.*)',t),axiom_reports=len(axioms)))
(e/'summary.json').write_text(json.dumps(dict(attempts=rows,lean_compiles=sum(x['exit'] is not None for x in rows),passes=sum(x['exit']==0 for x in rows),root_premises_removed=0,budget=dict(Lean=85,Kani=11)),indent=2)+'\n')
print([(x['attempt'],x['exit']) for x in rows])
