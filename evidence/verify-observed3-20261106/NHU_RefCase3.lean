import NHU_RefWords
set_option autoImplicit false
namespace AspisR1.NHU_RefCase3
open NHU_RefWords
theorem result (x : W×W) (left : Good x.1) (right : Good x.2) :
 (iRef (rRef x.2),iRef x.1)=ExtractedMaskTowerBasis.basisWords x 3 := by
 apply Prod.ext
 · exact (i_relation (rRef x.2) (r_good x.2 right).2).trans
    (congrArg ExtractedMaskTowerBasis.iWords (r_relation x.2 right))
 · exact i_relation x.1 left.2
#print axioms result
end AspisR1.NHU_RefCase3
