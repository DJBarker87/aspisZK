from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/port12count-20261024';T=R/'tools/port12count-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
configs=sorted(T.glob('lean-*.json'));assert len(configs)<=35
receipts={p.parent.name:json.loads(p.read_text()) for p in E.glob('lean-*/receipt.json')}
prior=R/'evidence/port11prov-20261024/manifest.json'
final={};attempts=[]
for cfg in configs:
 c=json.loads(cfg.read_text());a=c['attempt'];r=receipts.get(a)
 if r:
  attempts.append({k:r[k] for k in ['attempt','command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']})
  if r['exit_status']==0:
   for src,h in r['source_hashes'].items():
    if (L/src).exists() and hashlib.sha256((L/src).read_bytes()).hexdigest()==h:final[src]={'sha256':h,'attempt':a}
 else:
  attempts.append({'attempt':a,'status':'Reserved: no successful Lean receipt; conservatively counted','configuration':str(cfg.relative_to(R))})
x={'schema':'focused-extractor-proof-packet-v1','status':'Conditional actual-source authentication; both deployed targets not established','revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'inherited_lean_attempts':185,'new_lean_attempts':len(configs),'actual_lean_receipts':len(receipts),'cumulative_lean_attempts':185+len(configs),'lean_limit':220,'remaining_lean_attempts':35-len(configs),'kani_runs':0,'kani_limit':20,'prior_ledger':{'path':str(prior.relative_to(R)),'sha256':hashlib.sha256(prior.read_bytes()).hexdigest()},'final_sources':final,'attempts':attempts}
(E/'manifest.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:x[k] for k in ['new_lean_attempts','actual_lean_receipts','cumulative_lean_attempts','remaining_lean_attempts']}))
