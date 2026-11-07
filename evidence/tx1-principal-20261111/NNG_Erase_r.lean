import NNG_TreeSuffixes
import NNG_SourceSuffixes
import NNG_TraceCongruence
import NNG_Erase_mark2
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeErasure
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_TraceAlgebra
theorem erase_r {H W : Type} (c : Calls) (s : Parent H W) :
    erase (NNG_TreeSuffixes.f_r c s) = NNG_SourceSuffixes.f_r c s := by
  unfold NNG_TreeSuffixes.f_r NNG_SourceSuffixes.f_r
  rw [erase_bindM, NMT_CallTree.erase_invoke]
  apply result_congr
  intro r
  rw [erase_bindM, erase_liftM]
  apply result_congr
  intro cf
  cases cf with
  | Continue val => exact erase_mark2 c s val.1 val.2.1 val.2.2
  | Break residual => exact NNG_TraceAlgebra.erase_lift _
#print axioms erase_r
end AspisR1.NNG_TreeErasure
