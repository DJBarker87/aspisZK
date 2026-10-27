import PV_B1_ActualInstall
import PV_B1_PowersTotal
import PV_B1_Shift31
set_option autoImplicit false
noncomputable section
namespace PV_B1_254
open Aeneas Aeneas.Std Result
-- Complete Result identity, with no input or success hypothesis.
theorem source (N : Usize) (x : aspis_core.field.wide_exact.WideExact) :
    powers N x = PV_B1_PowersOriginal.weights.powers N x :=
  PV_B1_PowersBridge.op254_copy_equal_original N x
#print axioms source
end PV_B1_254
namespace PV_B1_Close254
open Aeneas Aeneas.Std Result ProverRwFull PV_B1_Transport PV_B1_ActualInstall
variable [ExternalTypes]
theorem selected_callback (ops : ExternalFuns) (N : Usize) (x : HW) :
    (selected ops).op254 N x = resultMap (arrayMap PV_B1_ActualCarrierWide.fromW)
      (PV_B1_PowersOriginal.weights.powers N (PV_B1_ActualCarrierWide.toW x)) :=
  op254_source ops N x

theorem nonfailure (ops : ExternalFuns) (N : Usize) (x : HW) :
    ∃ out, (selected ops).op254 N x=ok out := by
  obtain ⟨out,h⟩ := PV_B1_PowersTotal.total N (PV_B1_ActualCarrierWide.toW x)
  exact ⟨arrayMap PV_B1_ActualCarrierWide.fromW out,by change resultMap _ _ = _; rw [h]; rfl⟩

-- Exhibits an actual output at a nonempty array size; the row has no assumed law.
theorem nonvacuity (ops : ExternalFuns) (x : HW) :
    ∃ out : Array HW 1#usize, (selected ops).op254 1#usize x=ok out :=
  nonfailure ops 1#usize x

theorem observations (N : Usize) {O : Type} (observe : Result (Array HW N) → O)
    (ops : ExternalFuns) (x : HW) :
    observe ((selected ops).op254 N x) =
      observe (resultMap (arrayMap PV_B1_ActualCarrierWide.fromW)
        (PV_B1_PowersOriginal.weights.powers N (PV_B1_ActualCarrierWide.toW x))) :=
  congrArg observe (selected_callback ops N x)
#print axioms selected_callback
#print axioms nonfailure
#print axioms nonvacuity
#print axioms observations
end PV_B1_Close254
