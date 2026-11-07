import NNG_TreeSuffixes
import NNG_SourceSuffixes
import NNG_TraceCongruence
import NNG_Erase_r2
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeErasure
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_TraceAlgebra
theorem erase_r1 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) :
    erase (NNG_TreeSuffixes.f_r1 c s running alpha transcript1) = NNG_SourceSuffixes.f_r1 c s running alpha transcript1 := by
  unfold NNG_TreeSuffixes.f_r1 NNG_SourceSuffixes.f_r1
  rw [erase_bindM, NMT_CallTree.erase_invoke]
  apply result_congr
  intro r1
  rw [erase_bindM, erase_liftM]
  apply result_congr
  intro cf
  cases cf with
  | Continue val1 => exact erase_r2 c s running alpha transcript1 val1
  | Break residual => exact NNG_TraceAlgebra.erase_lift _
#print axioms erase_r1
end AspisR1.NNG_TreeErasure
