import RPz7_FIn_Primitives
import Port3_PushFrame
import Port4C_QueryArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotFieldLift
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide.Proof

theorem source (fm : Slice U8) (i : Usize) (value : AspisR1Stage2.Stage2Finish.E)
    (run : FIn_Primitives.field fm i=ok value)
    (canonical : Port4C_QueryArithmetic.CanonE value) :
    ∃ x,finishField fm i=ok x ∧ CanonicalFinish x := by
  unfold FIn_Primitives.field at run
  obtain ⟨x,call,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same := Result.ok.inj run
  have inverse : x=SAG_DotAdapter.toFinishE value := by
    rw [←same,SAG_DotAdapter.roundtrip_finishE]
  refine ⟨x,call,?_⟩
  rw [inverse]
  exact ⟨⟨⟨canonical.1.1,canonical.1.2.1⟩,canonical.1.2.2⟩,
    ⟨⟨canonical.2.1,canonical.2.2.1⟩,canonical.2.2.2⟩⟩
#print axioms source
end AspisR1.JGv_DotFieldLift
end
