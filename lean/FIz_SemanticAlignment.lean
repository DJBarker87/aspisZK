import FIz_ModelFamilies
import FIz_FamilyPacking
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_SemanticAlignment
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
open FIw_PublicModel (Public Openings Selectors)
/-- SAME native operands, retained scalarLaneAt meaning. Normalization remains
explicit here until derived from the original installed boxed reader. -/
theorem value (p : Public) (o : Openings) (s : Selectors)
    (hm : (∑ h : Fin 64, FIv_NativeArray.value s.high h.val)=1)
    (lm : (∑ l : Fin 16, FIv_NativeArray.value s.low l.val)=1) :
    FIy_NativeCoefficients.model p o s=
      fun j=>FIx_PreweightedPack.pack (fun i=>R0P.SemSource.scalarLaneAt
        (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) (4*j.val+i.val)) := by
  funext j
  rw [FIz_ModelFamilies.value p o s j hm lm,FIz_FamilyPacking.value]
#print axioms value
end AspisR1.FIz_SemanticAlignment
end
