from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/port10auth-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
rs=[json.loads(p.read_text()) for p in sorted(E.glob('lean-*/receipt.json'))]
prior=R/'evidence/port9oracle-20261024/manifest.json'
final={}
for r in rs:
 if r['exit_status']!=0:continue
 for src,h in r['source_hashes'].items():
  if (L/src).exists() and hashlib.sha256((L/src).read_bytes()).hexdigest()==h:final[src]={'sha256':h,'attempt':r['attempt']}
x={'schema':'focused-extractor-proof-packet-v1','status':'Focused source progress; both security targets not yet established','revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'inherited_lean_attempts':96,'new_lean_attempts':len(rs),'cumulative_lean_attempts':96+len(rs),'lean_limit':160,'remaining_lean_attempts':64-len(rs),'kani_runs':0,'kani_limit':20,'prior_ledger':{'path':str(prior.relative_to(R)),'sha256':hashlib.sha256(prior.read_bytes()).hexdigest()},'final_sources':final,'attempts':[{k:r[k] for k in ['attempt','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']} for r in rs]}
assert len(rs)<=64
(E/'manifest.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:x[k] for k in ['inherited_lean_attempts','new_lean_attempts','cumulative_lean_attempts','remaining_lean_attempts','kani_runs']}))
