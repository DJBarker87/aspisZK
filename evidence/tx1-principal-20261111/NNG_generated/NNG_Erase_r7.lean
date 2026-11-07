import NNG_TreeSuffixes
import NNG_SourceSuffixes
import NNG_TraceCongruence
import NNG_Erase_r8
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeErasure
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_TraceAlgebra
theorem erase_r7 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (transcript2 : r1_wire.SemanticTranscript H) (val4 : aspis_core.circle.SecureCirclePoint) :
    erase (NNG_TreeSuffixes.f_r7 c s alpha val1 val3 state_before_z0 transcript2 val4) = NNG_SourceSuffixes.f_r7 c s alpha val1 val3 state_before_z0 transcript2 val4 := by
  unfold NNG_TreeSuffixes.f_r7 NNG_SourceSuffixes.f_r7
  rw [erase_bindM, NMT_CallTree.erase_invoke]
  apply result_congr
  intro r7
  rw [erase_bindM, erase_liftM]
  apply result_congr
  intro cf
  cases cf with
  | Continue vr2 => exact erase_r8 c s alpha val1 val3 state_before_z0 transcript2 val4 vr2 r7
  | Break residual => exact NNG_TraceAlgebra.erase_lift _
#print axioms erase_r7
end AspisR1.NNG_TreeErasure
