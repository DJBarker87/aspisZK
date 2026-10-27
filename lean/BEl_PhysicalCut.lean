import BEl_NativeBatchCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_PhysicalCut
open Aeneas Aeneas.Std Result SdkC_Source

/-- A consumer for a FUTURE actual instrumented-body certificate. This premise
is displayed explicitly and is not discharged or installed in BEl_Top. The
reference-only BothSlots theorem must not be credited as the physical result. -/
theorem transfer {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest)
    (admitted : BEl_NativeBatchCut.Input → Fin 2 → S → Prop)
    (physical : BEl_NativeBatchCut.Input → Fin 2 → S → Log →
      BEh_Scope.Outcome S Unit AspisR1Stage2.verifier.Error)
    (bridge : ∀ input slot state before, admitted input slot state →
      physical input slot state before = BEl_NativeBatchCut.native call hashv input slot state before) :
    BEh_Scope.BothSlots admitted physical (BEl_NativeBatchCut.source call hashv) := by
  intro input slot state before valid
  rw [bridge input slot state before valid]
  exact BEl_NativeBatchCut.observation call hashv input slot state before trivial

#print axioms transfer
end AspisR1.BEl_PhysicalCut
end
