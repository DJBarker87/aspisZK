import SdkD_QueryBinding
import Uni_Cuts
import Port4B_FoldedCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_FoldedCut
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

/-- Keep the root copied by this exact TX1 suffix, together with its byte reads. -/
theorem suffix (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub proof : Slice U8) (split : Usize) (hash : Hash)
    (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (saved : alloc.vec.Vec U8)
    (start : compact.OFF_FOLDED_ROOT ops = ok 7751#usize)
    (finish : compact.OFF_ROUND1 ops = ok 7783#usize)
    (success : Tx1Reachability.afterPrepare ops D pub proof split hash none p g = ok (.Ok saved)) :
    ∃ (root : Array U8 32#usize) (view : Slice U8),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7751#usize,«end»:=7783#usize} = ok view ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view = ok (.Ok root) ∧
      ops.op6 D proof p root 0#usize hash = ok (.Ok ()) := by
  unfold Tx1Reachability.afterPrepare at success
  rw [start,finish] at success
  repeat' first
  | (solve | cases success)
  | uncase_result
  | head_reduce success
  | split at success
  all_goals exact ⟨_,_,by assumption,by assumption,by assumption⟩

theorem installed_constants (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    compact.OFF_FOLDED_ROOT (RowShape_InstalledSlots.verifierOps ops B std) = ok 7751#usize ∧
    compact.OFF_ROUND1 (RowShape_InstalledSlots.verifierOps ops B std) = ok 7783#usize := by
  have constants := ConcreteConstants.constants_total ops
  exact ⟨constants.2.2.2.2.2.2.1,constants.2.2.2.2.2.2.2⟩

#print axioms suffix
#print axioms installed_constants
end AspisR1.SdkD_FoldedCut
end
