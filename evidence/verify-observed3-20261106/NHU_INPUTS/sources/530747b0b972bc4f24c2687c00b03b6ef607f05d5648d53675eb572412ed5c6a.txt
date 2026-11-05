import NHU_RefWords
set_option autoImplicit false
namespace AspisR1.NHU_RefCase1
open NHU_RefWords
theorem result (x : W×W) (left : Good x.1) (right : Good x.2) :
 (iRef x.1,iRef x.2)=ExtractedMaskTowerBasis.basisWords x 1 :=
 Prod.ext (i_relation x.1 left.2) (i_relation x.2 right.2)
#print axioms result
end AspisR1.NHU_RefCase1
