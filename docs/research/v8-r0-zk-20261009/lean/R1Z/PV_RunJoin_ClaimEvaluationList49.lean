import R1Z.PV_RunJoin_ClaimImage48
import R1Z.PV_RunJoin_CoefficientTable48
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ClaimEvaluationList49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ClaimThread48 (Column W)
theorem complete (evaluate : Column → Result W) (p : Nat → Nat → W) (out : Nat → W)
    (hcell : ∀ l,l<29 → evaluate (PV_RunJoin_CoefficientsWeight46.column (p l))=ok (out l))
    (start n : Nat) (bound : start+n≤29) :
    PV_RunJoin_ClaimImage48.values evaluate (PV_RunJoin_CoefficientsWeight46.payload p start n)=
      ok (PV_RunJoin_OrderedList48.run out start n) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [PV_RunJoin_CoefficientsWeight46.payload,PV_RunJoin_ClaimImage48.values,hcell start (by omega)]
    simp only [bind_tc_ok]
    rw [ih (start+1) (by omega)]
    rfl
#print axioms complete
end R1Z.PV_RunJoin_ClaimEvaluationList49
