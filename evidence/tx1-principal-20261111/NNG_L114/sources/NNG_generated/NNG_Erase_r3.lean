import NNG_TreeSuffixes
import NNG_SourceSuffixes
import NNG_TraceCongruence
import NNG_Erase_mark3
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeErasure
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_TraceAlgebra
theorem erase_r3 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (r2 : core.result.Result Q aspis_core.state_only_prefix.r0.Error) :
    erase (NNG_TreeSuffixes.f_r3 c s running alpha transcript1 val1 r2) = NNG_SourceSuffixes.f_r3 c s running alpha transcript1 val1 r2 := by
  unfold NNG_TreeSuffixes.f_r3 NNG_SourceSuffixes.f_r3
  rw [erase_bindM, erase_liftM]
  apply result_congr
  intro r3
  rw [erase_bindM, erase_liftM]
  apply result_congr
  intro cf
  cases cf with
  | Continue val2 => exact erase_mark3 c s running val2 alpha transcript1 val1
  | Break residual => exact NNG_TraceAlgebra.erase_lift _
#print axioms erase_r3
end AspisR1.NNG_TreeErasure
