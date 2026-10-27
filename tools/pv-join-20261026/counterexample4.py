"""Retain the exact failed unrestricted source-to-reference ROW and provenance."""
from pathlib import Path
import json,hashlib,subprocess
r=Path(__file__).resolve().parents[2];e=r/'evidence/pv-join-20261026/resume4'
code="""from pathlib import Path
import json,hashlib
p=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/source/crates/aspis-core')
xs={str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(p.rglob('*.rs'))}
print(json.dumps(xs))
"""
q=subprocess.run(['ssh','-o','BatchMode=yes','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True,check=True);xs=json.loads(q.stdout)
local={f:hashlib.sha256((r/'crates/aspis-core'/f).read_bytes()).hexdigest() if (r/'crates/aspis-core'/f).is_file() else None for f in xs}
assert xs==local, [(f,x,local[f]) for f,x in xs.items() if x!=local[f]]
(e/'native-core-source-hashes.json').write_text(json.dumps(xs,indent=2)+'\n')
row=dict(op=121,status='checked counterexample to proposed unrestricted P6 Horner-reference row; no fix',source='aspis_core::state_only_sumcheck::evaluate_state_only_polynomial',reference='aspis_core::state_only_sumcheck::evaluate_state_only_polynomial_horner',statement='For every polynomial: [QM31; 28] and challenge: QM31, source(polynomial, challenge) = reference(polynomial, challenge)',input=dict(coefficients={'2':[1,0,0,0]},other_coefficients=[0,0,0,0],challenge=[0,2147483648,0,0]),source_output=[3,0,0,0],reference_output=[2147483646,0,0,0],native_receipt='poly-row-preflight4/receipt.json',kani_harness='row_counterexample::poly_raw_exact',kani_receipt='poly-row-counterexample4/receipt.json',core_all_rs_match_worktree=True,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),not_claimed=['fixture admitted input counterexample','privacy attack','direct self-equality of source with its own extraction is false'],reason_relevant='The requested row has arbitrary inputs and no desired-output premise. This reference cannot discharge that unrestricted row. The counterexample uses a noncanonical M31 raw limb; it must not be repaired by silently adding a canonical-input restriction.',endpoint_premises_removed=0)
(e/'op121-counterexample.json').write_text(json.dumps(row,indent=2)+'\n')
branches=['codex/cx-prover-rw-20261023','codex/pv-cb-20261026','codex/pv-cb3-20261026'];siblings=[]
for b in branches:
 rev=subprocess.check_output(['git','rev-parse',b],text=True).strip();files=subprocess.check_output(['git','ls-tree','-r','--name-only',b],text=True).splitlines();mods=[f for f in files if '/ProverRw20' in f and f.endswith('.lean')];log=subprocess.check_output(['git','log','-5','--oneline',b],text=True);siblings.append(dict(branch=b,revision=rev,ProverRw20_modules=mods,log=log,read_only=True))
(e/'sibling-stage2.json').write_text(json.dumps(siblings,indent=2)+'\n')
print('All host aspis-core Rust sources match worktree; unrestricted op121 P6 row retained.')
