from pathlib import Path
R=Path(__file__).resolve().parents[2];src=(R/'evidence/pv-canon-20261027/read-only/FullFuns.lean.txt').read_text();start=src.index('def host_sumcheck.prove_sumcheck_round\n');end=src.index('/-- [aspis_r1_cost_probe::host_sumcheck::prove_sumcheck_rounds]',start)
s=src[start:end].replace('def host_sumcheck.prove_sumcheck_round\n','def checked_round\n').replace('aspis_core.state_only_sumcheck.evaluate_state_only_polynomial\n              polynomial q1','checked_eval polynomial q1')
p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_Canon_CheckedRound.lean'
expected=('''import R1Z.PV_Canon_Carrier
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
/-- A domain monitor used only in proof code. Original evaluator is retained
on canonical arguments; this does not implement or replace shipped op121. -/
def checked_eval (p : Array aspis_core.field.QM31 28#usize)
    (q : aspis_core.field.QM31) : Result aspis_core.field.QM31 := by
  classical
  exact if Coeffs p ∧ Q q then aspis_core.state_only_sumcheck.evaluate_state_only_polynomial p q
    else .fail .panic
 theorem checked_eval_eq (p : Array aspis_core.field.QM31 28#usize)
    (q : aspis_core.field.QM31) (hp : Coeffs p) (hq : Q q) :
    checked_eval p q = aspis_core.state_only_sumcheck.evaluate_state_only_polynomial p q := by
  simp only [checked_eval,if_pos (And.intro hp hq)]
/-- Mechanical copy of the extracted round body, replacing exactly the one
op121 call by checked_eval. The generator asserts the unique replacement. -/
'''+s+'''\n#print axioms checked_eval_eq
end R1Z.PV_Canon
''')
if '--check' in __import__('sys').argv:
 assert p.read_text()==expected, 'monitored round differs from exact generated body'
else:p.write_text(expected)
assert src[start:end].count('aspis_core.state_only_sumcheck.evaluate_state_only_polynomial')==1
