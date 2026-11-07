import NNG_TreeSuffixes
import NNG_SourceSuffixes
import NNG_TraceCongruence
import NNG_Erase_mark5
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeErasure
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_TraceAlgebra
theorem erase_r9 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (transcript2 : r1_wire.SemanticTranscript H) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (vr3 : r1_wire.ValidatedRecord) :
    erase (NNG_TreeSuffixes.f_r9 c s alpha val1 val3 state_before_z0 transcript2 val4 val5 vr3) = NNG_SourceSuffixes.f_r9 c s alpha val1 val3 state_before_z0 transcript2 val4 val5 vr3 := by
  unfold NNG_TreeSuffixes.f_r9 NNG_SourceSuffixes.f_r9
  rw [erase_bindM, NMT_CallTree.erase_invoke]
  apply result_congr
  intro reply
  rcases reply with ⟨r9, transcript3⟩
  rw [erase_bindM, erase_liftM]
  apply result_congr
  intro cf
  cases cf with
  | Continue val6 => exact erase_mark5 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6
  | Break residual => exact NNG_TraceAlgebra.erase_lift _
#print axioms erase_r9
end AspisR1.NNG_TreeErasure
