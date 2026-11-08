import NMX_R4_BoxAction
set_option autoImplicit false
noncomputable section
namespace NMX_R4_BoxCoverage
open Aeneas Aeneas.Std Result AspisR1

/-- Every terminating std allocator outcome (including a rejected reserve)
has an identical complete Box observation in the Boolean realization. This is
representation of the retained std item, not an allocator-success premise. -/
theorem complete {A S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (size owner : Nat) (reservation : NP6_StdModel.Reservation)
 (decoded : core.result.Result A NKY_BoxAction.PE)
 (standard : (∃ post, a.allocate s size = .ok post) ∨ (∃ e, a.allocate s size = .fail e)) :
 ∃ aborts, NMX_R2_BoxActionObservation.view
   (NKY_BoxAction.run a s size reservation owner (.ok decoded)) =
   NMX_R2_NativeExecution.box aborts owner decoded := by
 cases decoded with
 | Err e => exact ⟨false,rfl⟩
 | Ok value =>
   rcases standard with ⟨post,returned⟩ | ⟨failure,stopped⟩
   · cases reservation with
     | Err e =>
       refine ⟨true,?_⟩
       simp only [NKY_BoxAction.run,NKY_BoxAction.newBox,returned,bind_tc_ok,bind_tc_fail,
        NMX_R2_BoxActionObservation.view,NMX_R2_NativeExecution.box] <;> rfl
     | Ok unit =>
       cases unit
       refine ⟨false,?_⟩
       simp only [NKY_BoxAction.run,NKY_BoxAction.newBox,returned,bind_tc_ok,bind_tc_fail,
        NMX_R2_BoxActionObservation.view,NMX_R2_NativeExecution.box] <;> rfl
   · refine ⟨true,?_⟩
     rw [NKY_BoxAction.allocator_failure _ _ _ _ _ _ _ stopped]
     rfl
#print axioms complete
end NMX_R4_BoxCoverage
end
