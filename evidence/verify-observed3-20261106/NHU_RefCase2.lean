import NHU_RefWords
set_option autoImplicit false
namespace AspisR1.NHU_RefCase2
open NHU_RefWords
theorem result (x : W×W) (right : Good x.2) :
 (rRef x.2,x.1)=ExtractedMaskTowerBasis.basisWords x 2 :=
 Prod.ext (r_relation x.2 right) rfl
#print axioms result
end AspisR1.NHU_RefCase2
