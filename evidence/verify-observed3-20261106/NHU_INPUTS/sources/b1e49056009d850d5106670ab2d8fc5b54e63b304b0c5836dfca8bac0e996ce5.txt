import NHU_Tower
import NHU_RefCase1
import NHU_RefCase2
import NHU_RefCase3
set_option autoImplicit false
namespace AspisR1.NHU_TowerPacket
open NHU_RefWords
/-- Complete four-branch word table. Keeping the finite table avoids normalizing
an entire function-valued match with large modulus expressions in the kernel. -/
theorem table (x : W×W) (left : Good x.1) (right : Good x.2) :
 x=ExtractedMaskTowerBasis.basisWords x 0 ∧
 (iRef x.1,iRef x.2)=ExtractedMaskTowerBasis.basisWords x 1 ∧
 (rRef x.2,x.1)=ExtractedMaskTowerBasis.basisWords x 2 ∧
 (iRef (rRef x.2),iRef x.1)=ExtractedMaskTowerBasis.basisWords x 3 :=
 ⟨rfl,NHU_RefCase1.result x left right,NHU_RefCase2.result x right,
 NHU_RefCase3.result x left right⟩
#print axioms table
end AspisR1.NHU_TowerPacket
