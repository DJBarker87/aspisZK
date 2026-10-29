import R1Z.PV_OWNI_RawOps
set_option autoImplicit false
namespace R1Z.PV_OWNI_WeightTotal
open Aeneas Aeneas.Std Result PV_OWNI_RawOps

def step (width pref : Nat) (acc : Q × Nat) (coordinate : Q) : Q × Nat :=
 (valueMul acc.1 (if pref.testBit (width-1-acc.2) then coordinate else valueSub one coordinate),acc.2+1)

theorem step_result (width pref : Nat) (acc : Q × Nat) (coordinate : Q) :
 PV_RDB2D_SparseWeights.step ops width pref acc coordinate=ok (step width pref acc coordinate) := by
 unfold PV_RDB2D_SparseWeights.step step
 cases h:pref.testBit (width-1-acc.2) <;>
  simp only [h,Bool.false_eq_true,if_false,if_true,sub,mul,bind_tc_ok]

theorem source_result (width pref : Nat) (coordinates : List Q) (acc : Q × Nat) :
 PV_RDB2D_SparseWeights.source ops width pref coordinates acc=
 ok (coordinates.foldl (step width pref) acc) := by
 induction coordinates generalizing acc with
 | nil => rfl
 | cons x xs ih =>
  rw [PV_RDB2D_SparseWeights.source,step_result]
  simp only [bind_tc_ok,List.foldl_cons]
  exact ih _
#print axioms step_result
#print axioms source_result
end R1Z.PV_OWNI_WeightTotal
