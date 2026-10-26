"""Read-only collection of native and admission receipts."""
from pathlib import Path
import json,subprocess,hashlib,re
root=Path(__file__).resolve().parents[2]
e=root/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/formatter262'
code='''from pathlib import Path
import json
r=Path('/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src')
files={}
for folder in (r/'receipts').glob('pdict262-*'):
 for p in folder.iterdir():
  if p.is_file():files['native/'+folder.name+'/'+p.name]=p.read_text()
for pattern in ['reservation-formatter262-*','launch-pdict262-*']:
 for p in r.glob(pattern):
  if p.is_file():files['admission/'+p.name]=p.read_text()
print(json.dumps(files))
'''
# sh quote only the fixed read-only program, with no interpolation of source data.
cmd="python3 -c '"+code.replace("'","'\\''")+"'"
files=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90',cmd],text=True))
for name,text in files.items():
 p=e/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
rows=[]
for p in sorted((e/'native').glob('*/receipt.json')):
 x=json.loads(p.read_text());rows.append({k:x.get(k) for k in ['attempt','target','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','cgroup_swap_peak_bytes','cgroup_memory_events','source_revision','print_axioms']})
(e/'native-summary.json').write_text(json.dumps(dict(runs=rows,kani_runs=len(rows),qualification='Missing-Cargo launch and admission refusal precede Kani and are uncharged. Compiler errors after cargo kani invocation are charged. GNU time RSS under timeout can undercount descendants; cgroup peak is recorded separately.'),indent=2)+'\n')
if rows:
 p=e/'native/pdict262-kani-001-retry1/receipt.json'
 if p.exists():
  x=json.loads(p.read_text());bindings=[]
  for name,digest in x['source_sha256'].items():
   if not name.startswith(('crates/aspis-core/','crates/aspis-r1-cost-probe/','crates/aspis-prover/','crates/aspis-statement/')):continue
   local=root/name
   bindings.append(dict(path=name,host_sha256=digest,local_sha256=hashlib.sha256(local.read_bytes()).hexdigest() if local.is_file() else None))
  (e/'production-source-binding.json').write_text(json.dumps(dict(inputs=bindings,mismatches=[b for b in bindings if b['local_sha256']!=b['host_sha256']]),indent=2)+'\n')
print('Kani invoked',len(rows),[(x['attempt'],x['exit_status']) for x in rows])
