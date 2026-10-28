"""Read-only native/constructor scope inspection. Absence is not a Lean theorem."""
import subprocess,json,hashlib
from pathlib import Path
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjdec-20261028';rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
paths=['docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_'+n+'.lean' for n in ['Deployed','SourceConstructor','LedgerConstructor','InstalledEndpoint','CommonSample32','CommonObserver32','InstalledFamily']]
paths+=['tools/r1-cost-probe/src/bin/devnet_spend.rs','tools/r1-cost-probe/src/bin/devnet_spend/plan.rs','tools/r1-cost-probe/src/bin/devnet_spend/Client64_accounts.rs','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs']
records=[]
for p in paths:
 b=subprocess.check_output(['git','show',rev+':'+p]);text=b.decode();records.append(dict(path=p,git_blob=subprocess.check_output(['git','rev-parse',rev+':'+p],text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),lines=[dict(line=i,text=l) for i,l in enumerate(text.splitlines(),1) if any(n in l for n in ['disclosed','observerOracle','(oracle :','semantic_public','prove_for_proof_accounts','prove_wall_seconds','statement.bin'])]))
scan=subprocess.run(['git','grep','-n','disclosed\|observerOracle',rev,'--','tools/r1-cost-probe','crates/aspis-r1-cost-probe','crates/aspis-prover'],text=True,capture_output=True)
(E/'d420-native-installation-audit.json').write_text(json.dumps(dict(revision=rev,records=records,native_symbol_search=dict(command=scan.args,exit=scan.returncode,stdout=scan.stdout,stderr=scan.stderr),scope='Source inspection only. Forwarding constructors do not establish a native observation installation. No deployed counterexample is claimed.'),indent=2)+'\n')
print('Recorded exact constructor and deployed source hashes')
