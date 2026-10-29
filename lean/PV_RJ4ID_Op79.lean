import R1Z.PV_DL_EncoderNative
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4ID_Op79
open Aeneas Aeneas.Std Result ProverRwFull

/-- Complete Result equality between the retained native forward chunks/zip
interpretation and the control installed by runjoin. The deployed source
binding and compiler-preservation boundary are recorded separately. -/
theorem native_control {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) :
    PV_DL_EncoderNative.value inst q p = PV_DL_EncoderControl.value inst q p :=
  (PV_DL_EncoderNative.source_reference inst q p).trans
    (PV_DL_EncoderControl.source_reference inst q p)

variable [ExternalTypes]

/-- Interpret the statically called encoder by its retained native loop model.
This definition alone makes no deployed-code association claim. -/
def native (ops : ExternalFuns) : ExternalFuns :=
  {ops with op79 := fun inst q p => PV_DL_EncoderNative.value inst q p}

/-- Exactly the op79 installation used by ClaimEvaluator48/ClaimEvaluation49,
with all other incoming dictionary entries preserved. -/
theorem installation (ops : ExternalFuns) :
    native ops = PV_DL_EncoderSelected.selected ops := by
  have entry :
      (fun {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
        (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) =>
        PV_DL_EncoderNative.value inst q p) =
      (fun {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
        (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) =>
        PV_DL_EncoderControl.value inst q p) := by
    funext E inst q p
    exact native_control inst q p
  unfold native PV_DL_EncoderSelected.selected
  rw [entry]

#print axioms native_control
#print axioms installation
end R1Z.PV_RJ4ID_Op79
