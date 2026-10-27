import PV_B1_ActualInstall
set_option autoImplicit false
noncomputable section
namespace PV_B1_230
open Aeneas Aeneas.Std Result
theorem source (xs : Slice aspis_core.field.QM31) :
    state_only_copy_helper_sum xs=ok (PV_B1_SumOriginal.original_row xs) :=
  PV_B1_SumOriginal.op230_source xs
#print axioms source
end PV_B1_230
namespace PV_B1_Close230
open Aeneas Aeneas.Std Result ProverRwFull PV_B1_Transport PV_B1_ActualInstall
variable [ExternalTypes]
theorem selected_callback (ops : ExternalFuns) (xs : Slice HQ) :
    (selected ops).op230 xs=ok (Option.map PV_B1_ActualCarrier230.fromQ
      (PV_B1_SumOriginal.original_row (sliceMap PV_B1_ActualCarrier230.toQ xs))) :=
  op230_source ops xs

theorem nonvacuity (ops : ExternalFuns) (x : HQ) :
    ∃ y, (selected ops).op230 (⟨List.replicate 1024 x,by simp only [List.length_replicate]; scalar_tac⟩ : Slice HQ)=ok (some y) := by
  let xs : Slice HQ := ⟨List.replicate 1024 x,by simp only [List.length_replicate]; scalar_tac⟩
  have h : Slice.len (sliceMap PV_B1_ActualCarrier230.toQ xs)=1024#usize := by
    rw [slice_length]; apply UScalar.eq_of_val_eq
    simp only [Slice.len_val,Slice.length,xs,List.length_replicate]; rfl
  have hs := selected_callback ops xs
  unfold PV_B1_SumOriginal.original_row at hs
  rw [if_pos h] at hs
  exact ⟨_,hs⟩
#print axioms selected_callback
#print axioms nonvacuity
end PV_B1_Close230
