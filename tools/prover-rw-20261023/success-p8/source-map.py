"""Check pending-source promotion; no build or infrastructure changes."""
from pathlib import Path
import hashlib,json
r=Path(__file__).resolve().parents[3]
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023'
names=['ProverRwP7CoefficientsSource','ProverRwP7CoefficientsInstall','ProverRwP7BodyCoefficients','ProverRwP7CurrentComplexBridge']
rows=[]
for n in names:
 old=(e/'success-p7/pending'/(n+'.lean.txt')).read_text();current=(r/'docs/research/v8-r0-zk-20261009/lean/R1Z'/('PV_'+n+'.lean')).read_text()
 renamed=old
 for t in names:renamed=renamed.replace(t,'PV_'+t)
 # Added proofs are independent declarations, not modifications of source bodies.
 if n.endswith('CoefficientsSource'):
  end='-- Expose the complete generic source equation'
  assert current.split(end)[0]==renamed.split('end R1Z.PV_ProverRwP7CoefficientsSource')[0]
 elif n.endswith('CoefficientsInstall'):
  assert current.split('theorem fibre_preserved')[0]==renamed.split('#print axioms source')[0]
 else:assert current==renamed
 rows.append(dict(module='PV_'+n,pending_sha256=hashlib.sha256(old.encode()).hexdigest(),current_sha256=hashlib.sha256(current.encode()).hexdigest(),change='Namespace/import PV_ rename; new standalone proof declarations only'))
(e/'success-p8/source-map.json').write_text(json.dumps(rows,indent=2)+'\n')
print('4 pending promotions checked; source bodies unchanged after namespace renaming')
