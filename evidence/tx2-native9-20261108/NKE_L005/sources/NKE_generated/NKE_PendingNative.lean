import NKE_Stores
import NJR_ReservationRaw
import NJJ_PendingStep
set_option autoImplicit false
noncomputable section
namespace NKE_PendingNative
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
abbrev Row := Port3_NativePendingBody.Row
abbrev K := aspis_core.field.QM31
/-- G folds the actual one-row native store; the allocation is retained separately. -/
def states (weights : Slice K) (before : alloc.vec.Vec Row) (n : Nat) : alloc.vec.Vec Row :=
 ⟨NKE_Stores.G (weights.val.map Port3_PendingInstall.row) before.val n,
  by rw [NKE_Stores.length];exact before.property⟩

theorem cut (weights : Slice K) (before : alloc.vec.Vec Row)
 (width : weights.val.length=64) (rawWidth : before.val.length=64)
 (i : Nat) (inside : i<64) :
 NJR_Cuts.pending weights (states weights before i) (states weights before (i+1)) i (i+1) := by
 refine ⟨rfl,?_,?_⟩
 · change (NKE_Stores.G _ _ _).length=64
   rw [NKE_Stores.length,rawWidth]
 · intro j hj
   change (NKE_Stores.G _ _ (i+1))[j]?=_
   rw [NKE_Stores.step _ _ (by simp only [List.length_map,width,rawWidth]) i (by omega) j (by omega)]
   by_cases same : i=j
   · subst j;simp only [if_pos rfl,List.getElem?_map]
   · simp only [if_neg same];rfl

theorem source (reservation : NP6_StdModel.Reservation) (weights : Slice K)
 (before : alloc.vec.Vec Row) (width : weights.val.length=64) (rawWidth : before.val.length=64) :
 NJJ_Common.pending reservation weights=
 match reservation with
 | .Ok () => ok (.Ok (⟨states weights before 64,0#usize⟩ : verifier.BatchedWeights))
 | .Err _ => ok (.Err .Allocation) := by
 unfold NJJ_Common.pending
 rw [NJJ_Pending.source _ weights width (states weights before)
  (fun _ i hi=>cut weights before width rawWidth i hi)]
 cases reservation with
 | Ok unit => cases unit;rfl
 | Err error => rfl
#print axioms cut
#print axioms source
end NKE_PendingNative
