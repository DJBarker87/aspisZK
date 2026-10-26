import R1Z.PV_CB_Composition
import R1Z.PV_CB_OwnedEncoder
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_EncoderInstall
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- Extracted owned reference; the native correspondence gate is recorded
separately and is not inferred from this equation. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_CB_Composition.selected ops with op79 := PV_CB_OwnedEncoder.owned.encoder}
theorem source (ops : ExternalFuns) {E : Type}
    (inst : aspis_core.r0.scalar.CodeField E) (q : Array E 1024#usize)
    (p : aspis_core.r0.domain.Point E) :
    (selected ops).op79 inst q p = PV_CB_OwnedEncoder.owned.encoder inst q p := rfl
theorem callback_removed (ops other : ExternalFuns) {E : Type}
    (inst : aspis_core.r0.scalar.CodeField E) (q : Array E 1024#usize)
    (p : aspis_core.r0.domain.Point E) :
    (selected {ops with op79 := other.op79}).op79 inst q p =
      (selected ops).op79 inst q p := rfl
#print axioms source
#print axioms callback_removed
end R1Z.PV_CB_EncoderInstall
