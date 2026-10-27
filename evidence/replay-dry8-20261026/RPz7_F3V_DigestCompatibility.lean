import RPz7_F3V_RunEvidence
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_DigestCompatibility
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem same {F C : Type} (c : DrvC_Installation.Configuration F C) (H : Bytes → State) :
    Tx1Q_Install.digest (F3V_RunEvidence.D1 c H)=F3V_RunEvidence.D2 c H := rfl

theorem realization (H : Bytes → State) : S2W_ExtractionBoundary.P1 H H := by
  constructor
  intro q
  rfl

#print axioms same
#print axioms realization
end AspisR1.F3V_DigestCompatibility
end
