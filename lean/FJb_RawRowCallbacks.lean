import FJa_PoseidonPow5
import RawPoseidonExternalAllRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_RawRowCallbacks
open Aeneas Aeneas.Std Result FIq_Native
abbrev Input := Array (Array U32 4#usize) 4#usize
abbrev call := state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
abbrev reference := AspisR1SelectedMaskProbe.state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
theorem same (input : Input) (output limb : Usize) :
    call (input,output) limb=reference (input,output) limb := rfl
/-- Every selected raw-row callback is stable; this is derived from the
same concrete scalar body, with array reads guaranteed by the dimensions. -/
theorem total (input : Input) (output limb : Usize)
    (ho : output.val < 4) (hi : limb.val < 4) :
    ∃ x,call (input,output) limb=ok (x,(input,output)) := by
  obtain ⟨z0,z1,z2,z3,h0,_,h1,_,h2,_,h3,_⟩ :=
    RawPoseidonExternalAllRows.call_mut_all_lanes_of_array_bounds input limb hi
  have hc : output.val=0 ∨ output.val=1 ∨ output.val=2 ∨ output.val=3 := by omega
  rcases hc with h | h | h | h
  · have e : output=0#usize := UScalar.eq_of_val_eq h
    subst output
    exact ⟨z0,(same input 0#usize limb).trans h0⟩
  · have e : output=1#usize := UScalar.eq_of_val_eq h
    subst output
    exact ⟨z1,(same input 1#usize limb).trans h1⟩
  · have e : output=2#usize := UScalar.eq_of_val_eq h
    subst output
    exact ⟨z2,(same input 2#usize limb).trans h2⟩
  · have e : output=3#usize := UScalar.eq_of_val_eq h
    subst output
    exact ⟨z3,(same input 3#usize limb).trans h3⟩
#print axioms same
#print axioms total
end AspisR1.FJb_RawRowCallbacks
end
