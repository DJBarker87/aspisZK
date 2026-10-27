import FIz_PublicDigest
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_DigestFamily
open FIw_PublicModel (Public Openings Selectors)
theorem value (p : Public) (o : Openings) (s : Selectors) :
    List.ofFn (FIy_PublicDigest.model p o s)=R0P.digestFamily.residuals
      (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,R0P.digestFamily,List.length_ofFn]
    rfl
  · intro j hj hj1
    simp only [List.getElem_ofFn,R0P.digestFamily,List.getElem_ofFn]
    rw [FIz_PublicDigest.value]
#print axioms value
end AspisR1.FIz_DigestFamily
end
