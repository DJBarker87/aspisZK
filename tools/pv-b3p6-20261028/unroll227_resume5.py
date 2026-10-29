"""Emit only fixed short loop-shape laws; arithmetic operands remain symbolic."""
from pathlib import Path
D=Path('evidence/pv-b3p6-20261028/lean');out=['import PV_B3P_Ordered227\nnamespace PV_B3P_Unroll227\nopen Aeneas Aeneas.Std PV_B3P_Ordered227\nset_option autoImplicit false\n']
for n in (3,4,7,8,10,16,20,21,24,33):
 body='    do\n';prev='initial'
 for i in range(n):
  body+=f'      let next{i} ← step {prev} (start+{i})\n';prev=f'next{i}'
 body+=f'      .ok {prev}'
 out.append(f'theorem forward_{n} {{α : Type}} (step : α → Nat → Result α) (start : Nat) (initial : α) :\n    fold step (List.range\' start {n}) initial = ({body}) := by\n  simp only [List.range\'_succ,fold]\n  rfl\n#print axioms forward_{n}\n')
out.append('end PV_B3P_Unroll227\n');(D/'PV_B3P_Unroll227.lean').write_text('\n'.join(out))
