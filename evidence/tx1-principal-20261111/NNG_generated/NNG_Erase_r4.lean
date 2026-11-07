import NNG_TreeSuffixes
import NNG_SourceSuffixes
import NNG_TraceCongruence
import NNG_Erase_r5
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeErasure
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_TraceAlgebra
theorem erase_r4 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (mask : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) :
    erase (NNG_TreeSuffixes.f_r4 c s running val2 mask alpha transcript1 val1) = NNG_SourceSuffixes.f_r4 c s running val2 mask alpha transcript1 val1 := by
  unfold NNG_TreeSuffixes.f_r4 NNG_SourceSuffixes.f_r4
  rw [erase_bindM, NMT_CallTree.erase_invoke]
  apply result_congr
  intro r4
  rw [erase_bindM, erase_liftM]
  apply result_congr
  intro cf
  cases cf with
  | Continue vr => exact erase_r5 c s running val2 mask alpha transcript1 val1 vr r4
  | Break residual => exact NNG_TraceAlgebra.erase_lift _
#print axioms erase_r4
end AspisR1.NNG_TreeErasure
