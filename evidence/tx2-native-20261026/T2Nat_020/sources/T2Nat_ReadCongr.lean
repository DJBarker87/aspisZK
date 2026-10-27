import T2Nat_ScalarJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_ReadCongr
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_ResultEq CheckpointBytes4Sections

theorem withK {T : Type} (left right : ReadK)
    (same : ∀ r, EqOk (left r) (right r)) (r : verifier.Reader)
    (k l : K → verifier.Reader → Result (core.result.Result T verifier.Error))
    (next : ∀ x out, EqOk (k x out) (l x out)) :
    EqOk (CheckpointBytes4Ops.withK left r k) (CheckpointBytes4Ops.withK right r l) := by
  unfold CheckpointBytes4Ops.withK
  apply T2Nat_ResultEq.bind (same r)
  intro pair
  rcases pair with ⟨value,out⟩
  cases value with
  | Err e => exact T2Nat_ResultEq.refl _
  | Ok x => exact next x out

#print axioms withK
end AspisR1.T2Nat_ReadCongr
end
