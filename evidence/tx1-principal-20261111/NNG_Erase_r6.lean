import NNG_TreeSuffixes
import NNG_SourceSuffixes
import NNG_TraceCongruence
import NNG_Erase_r7
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeErasure
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_TraceAlgebra
theorem erase_r6 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (vr1 : r1_wire.ValidatedRecord) :
    erase (NNG_TreeSuffixes.f_r6 c s alpha transcript1 val1 val3 state_before_z0 vr1) = NNG_SourceSuffixes.f_r6 c s alpha transcript1 val1 val3 state_before_z0 vr1 := by
  unfold NNG_TreeSuffixes.f_r6 NNG_SourceSuffixes.f_r6
  rw [erase_bindM, NMT_CallTree.erase_invoke]
  apply result_congr
  intro reply
  rcases reply with ⟨r6, transcript2⟩
  rw [erase_bindM, erase_liftM]
  apply result_congr
  intro cf
  cases cf with
  | Continue val4 => exact erase_r7 c s alpha val1 val3 state_before_z0 transcript2 val4
  | Break residual => exact NNG_TraceAlgebra.erase_lift _
#print axioms erase_r6
end AspisR1.NNG_TreeErasure
