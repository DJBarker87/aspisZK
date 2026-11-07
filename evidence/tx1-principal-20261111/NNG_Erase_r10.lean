import NNG_TreeSuffixes
import NNG_SourceSuffixes
import NNG_Erase_r11
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeErasure
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_TraceAlgebra
theorem erase_r10 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) :
    erase (NNG_TreeSuffixes.f_r10 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6) = NNG_SourceSuffixes.f_r10 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 := by
  unfold NNG_TreeSuffixes.f_r10 NNG_SourceSuffixes.f_r10
  rw [erase_bindM, NMT_CallTree.erase_invoke]
  apply result_congr
  intro reply
  rw [erase_bindM, erase_liftM]
  apply result_congr
  intro cf
  cases cf with
  | Continue val7 => exact erase_r11 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 val7
  | Break residual => exact NNG_TraceAlgebra.erase_lift _
#print axioms erase_r10
end AspisR1.NNG_TreeErasure
