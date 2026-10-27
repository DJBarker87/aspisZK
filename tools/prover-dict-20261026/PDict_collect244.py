"""Read-only focused evidence collection. Does not launch or alter host jobs."""
from pathlib import Path
import subprocess,json,hashlib,re
root=Path(__file__).resolve().parents[2]
e=root/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/world244'
script='''from pathlib import Path
import json
job=Path('/home/dombarker/project-offloads/codex-cx-prover-dict-20261026')
files={}
for p in (job/'receipts244').glob('*'):
 if p.is_file():files['lean/'+p.name]=p.read_text()
for a in range(24400,24700):
 for tag in ['out','time','sha']:
  p=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')/f'{tag}-{a}.log'
  if tag=='sha':p=p.with_suffix('.txt')
  if p.is_file():files['lean/'+p.name]=p.read_text()
for p in (job/'src/receipts').glob('pdict244-*/*'):
 if p.is_file() and p.suffix in ['.json','.log']:
  files['native/'+p.parent.name+'/'+p.name]=p.read_text()
for p in (job/'src').glob('reservation-pdict244-*'):
 if p.is_file():files['admission/'+p.name]=p.read_text()
for p in (job/'src').glob('launch-244-*'):
 if p.is_file():files['admission/'+p.name]=p.read_text()
for p in job.glob('launch-244*.log'):
 if p.is_file():files['admission/'+p.name]=p.read_text()
print(json.dumps(files))
'''
files=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-c',"'"+script.replace("'","'\\''")+"'"],text=True))
for name,s in files.items():
 p=e/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
rows=[]
for p in sorted((e/'lean').glob('*-input.json')):
 x=json.loads(p.read_text());a=x['attempt'];s=(e/'lean'/f'{a}.lean.txt').read_text()
 assert hashlib.sha256(s.encode()).hexdigest()==x['source_sha256']
 out=e/'lean'/f'out-{a}.log'
 if not out.exists():continue
 log=out.read_text();t=(e/'lean'/f'time-{a}.log').read_text()
 status=int(re.search(r'^exit=(\d+)',log,re.M)[1])
 reports=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)
 if status==0:
  assert 'sorryAx' not in log and 'error:' not in log
  for z in reports:
   if 'depends on axioms: [' in z:
    assert set(v.strip() for v in z.split('depends on axioms: [')[1][:-1].replace('\n','').split(','))<={'propext','Classical.choice','Quot.sound'}
 x.update(exit_status=status,command=f"sh {x['launcher']} {a} {x['module']} J 7000 8 {x['deps_fingerprint']}",time_log=t,print_axioms=reports,errors=[z for z in log.splitlines() if 'error:' in z])
 (e/'lean'/f'{a}-receipt.json').write_text(json.dumps(x,indent=2)+'\n');rows.append({k:x[k] for k in ['attempt','module','exit_status','source_sha256','print_axioms','errors','time_log']})
(e/'lean-summary.json').write_text(json.dumps(dict(host_compiles=len(rows),local_invocations=len(list((e/'local').glob('*-receipt.json'))),compiles=len(rows)+len(list((e/'local').glob('*-receipt.json'))),remaining=81-len(rows)-len(list((e/'local').glob('*-receipt.json'))),attempts=rows,qualification='Focused source validation only; no frozen release replay.'),indent=2)+'\n')
native=[]
for p in sorted((e/'native').glob('pdict244-*/receipt.json')):
 x=json.loads(p.read_text());native.append({k:x.get(k) for k in ['attempt','target','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms','limits','expected_work']})
(e/'native-summary.json').write_text(json.dumps(dict(runs=native,kani_runs=sum('kani' in r['target'] for r in native),qualification='Admission refusals and PATH failures before cargo are not Kani invocations. Native scope peaks across a batch are cumulative; raw GNU time is per target.'),indent=2)+'\n')
print('Host Lean',len(rows),'Local Lean',len(list((e/'local').glob('*-receipt.json'))),'Kani',sum('kani' in r['target'] for r in native))
