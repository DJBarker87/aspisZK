import NMC_LocalWindows
import NMC_RootComplement
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_RootStages
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NMC_Window
structure Tried (A : Type) where
 before : Context A
 payload : Slice U8
 attempted : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError
def tryStage {A : Type} (before : Context A) (payload : Slice U8) : Result (Tried A) := do
 let attempted ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload
 ok ⟨before,payload,attempted⟩
inductive UnwrapOutcome (A : Type) where
 | returned (root : Array U8 32#usize) (after : Context A)
 | aborted (error : Error) (lastEntered : Tried A)
 | diverged (lastEntered : Tried A)
def unwrapStage {A : Type} (entered : Tried A) : UnwrapOutcome A :=
 match S1SemanticRootCopy.unwrapRoot entered.attempted with
 | .ok root=>.returned root entered.before
 | .fail error=>.aborted error entered
 | .div=>.diverged entered
/-- Off exact32 extent, try_from returns Err before unwrap aborts. The last
entered state includes THAT attempted Err, original payload and SAME parent
heap/allocator/Box/destination regions. No cleanup or new post is fabricated. -/
theorem wrong_length {A : Type} (before : Context A) (payload : Slice U8)
 (bad : payload.length≠32) :
 ∃ entered,tryStage before payload=ok entered ∧ unwrapStage entered=.aborted .panic entered ∧
 entered.before=before ∧ entered.payload=payload ∧ entered.attempted=.Err () := by
 have attempted : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload=ok (.Err ()) := by
  simp only [core.array.TryFromArrayCopySlice.try_from,show ¬payload.length=(32#usize).val from bad,dif_neg]
  rfl
 refine ⟨⟨before,payload,.Err ()⟩,?_,rfl,rfl,rfl,rfl⟩
 simp only [tryStage,attempted,bind_tc_ok]
/-- An aborting unwrap preserves its exact entered suboccurrence state,
which is more precise than the preceding major rootCopy marker. -/
theorem abort_frontier {A : Type} (entered : Tried A) (error : Error)
 (aborted : S1SemanticRootCopy.unwrapRoot entered.attempted=fail error) :
 unwrapStage entered=.aborted error entered := by simp only [unwrapStage,aborted]
#print axioms wrong_length
#print axioms abort_frontier
set_option pp.proofs false in #print wrong_length
end AspisR1.NMC_RootStages
end
