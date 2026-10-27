import RPv_FJe_PackedLoopValue
import RPv_FJe_ExternalSum
import RPv_FJe_ExternalMap
import RPv_FJe_PackedGroupModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_ExternalPackedValue
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
open FJe_ExternalCalls (Packed)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
/-- COMPLETE original native external_linear_packed VALUE on the SAME input.
The Kani raw bridge is independently retained;this source proof adds no trust
or equality premise for any local result. -/
theorem value (s : State) (out : Packed) (hs : canonical s)
    (run : state_only_poseidon.external_linear_packed s=ok out) :
    canonical out ∧ decoded out=fun g=>R0P.poseidonPackingFormula iBasis uBasis
      (fun j=>R0P.poseidonExternalLinear (decoded s) (FJe_ExternalAdjoint.lane g j)) := by
  obtain ⟨p,total,rp,rt,tail⟩ := FJe_ExternalCalls.reached s out run
  have zero : canonical (Array.repeat 4#usize field.QM31.ZERO) := by
    intro x hx
    rw [(List.mem_replicate.mp hx).2]
    exact FIv_NativeValue.zero.1
  have vp := FJe_PackedLoopValue.value 4 0#usize s
    (Array.repeat 4#usize field.QM31.ZERO) p rfl hs zero rp
  have ep : decoded p=FJe_PackedGroupStep.localModel s := by
    funext j
    have hv := vp.2 j
    have cond : (0#usize).val≤j.val := by change 0≤j.val;exact Nat.zero_le _
    simpa only [if_pos cond] using hv
  have vs := FJe_ExternalSum.value p total vp.1 rt
  have vm := FJe_ExternalMap.value p out total vp.1 vs.1 tail
  refine ⟨vm.1,?_⟩
  funext g
  have vg := congrFun vm.2 g
  rw [vs.2] at vg
  unfold FJe_ExternalSum.model at vg
  rw [ep,FJe_PackedGroupModel.value] at vg
  apply vg.trans
  exact FJe_ExternalAdjoint.value iBasis uBasis (decoded s) g
#print axioms value
end AspisR1.FJe_ExternalPackedValue
end
