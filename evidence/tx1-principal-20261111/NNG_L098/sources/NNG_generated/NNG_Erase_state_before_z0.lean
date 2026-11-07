import NNG_TreeSuffixes
import NNG_SourceSuffixes
import NNG_TraceCongruence
import NNG_Erase_r6
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeErasure
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_TraceAlgebra
theorem erase_state_before_z0 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) :
    erase (NNG_TreeSuffixes.f_state_before_z0 c s alpha transcript1 val1 val3 r4) = NNG_SourceSuffixes.f_state_before_z0 c s alpha transcript1 val1 val3 r4 := by
  unfold NNG_TreeSuffixes.f_state_before_z0 NNG_SourceSuffixes.f_state_before_z0
  rw [erase_bindM, NMT_CallTree.erase_invoke]
  apply result_congr
  intro state_before_z0
  rw [erase_bindM, erase_liftM]
  apply result_congr
  intro cf
  cases cf with
  | Continue vr1 => exact erase_r6 c s alpha transcript1 val1 val3 state_before_z0 vr1
  | Break residual => exact NNG_TraceAlgebra.erase_lift _
#print axioms erase_state_before_z0
end AspisR1.NNG_TreeErasure
