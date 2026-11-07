import NNG_TreeSuffixes
import NNG_SourceSuffixes
import NNG_TraceCongruence
import NNG_Erase_r9
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeErasure
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_TraceAlgebra
theorem erase_r8 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (transcript2 : r1_wire.SemanticTranscript H) (val4 : aspis_core.circle.SecureCirclePoint) (vr2 : r1_wire.ValidatedRecord) (r7 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) :
    erase (NNG_TreeSuffixes.f_r8 c s alpha val1 val3 state_before_z0 transcript2 val4 vr2 r7) = NNG_SourceSuffixes.f_r8 c s alpha val1 val3 state_before_z0 transcript2 val4 vr2 r7 := by
  unfold NNG_TreeSuffixes.f_r8 NNG_SourceSuffixes.f_r8
  rw [erase_bindM, NMT_CallTree.erase_invoke]
  apply result_congr
  intro r8
  rw [erase_bindM, erase_liftM]
  apply result_congr
  intro cf
  cases cf with
  | Continue val5 =>
    rw [erase_bindM, erase_liftM]
    apply result_congr
    intro cf9
    cases cf9 with
    | Continue vr3 => exact erase_r9 c s alpha val1 val3 state_before_z0 transcript2 val4 val5 vr3
    | Break residual => exact NNG_TraceAlgebra.erase_lift _
  | Break residual => exact NNG_TraceAlgebra.erase_lift _
#print axioms erase_r8
end AspisR1.NNG_TreeErasure
