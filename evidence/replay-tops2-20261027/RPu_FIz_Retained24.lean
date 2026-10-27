import RPu_FIz_SemanticAlignment
import RPu_FIz_ConcretePack
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_Retained24
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
open FIw_PublicModel (Public Openings Selectors)
theorem value (p : Public) (o : Openings) (s : Selectors)
    (hm : (∑ h : Fin 64, FIv_NativeArray.value s.high h.val)=1)
    (lm : (∑ l : Fin 16, FIv_NativeArray.value s.low l.val)=1) :
    (fun j=>FIz_ConcretePack.embed (FIy_NativeCoefficients.model p o s j))=
      fun j=>R0P.pack4 ConcretePackBasis.basis (fun i=>FIz_ConcretePack.embed (R0P.SemSource.scalarLaneAt
        (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) (4*j.val+i.val))) := by
  rw [FIz_SemanticAlignment.value p o s hm lm]
  funext j
  exact FIz_ConcretePack.value _
#print axioms value
end AspisR1.FIz_Retained24
end
