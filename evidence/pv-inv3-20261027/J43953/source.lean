import R1Z.PV_Inv_MaskTail48
import R1Z.PV_Inv_MaskTail49
import R1Z.PV_Inv_MaskTail50
import R1Z.PV_Inv_MaskTail51
import R1Z.PV_Inv_MaskTail52
import R1Z.PV_Inv_MaskTail53
import R1Z.PV_Inv_MaskTail54
import R1Z.PV_Inv_MaskTail55
import R1Z.PV_Inv_MaskTail56
import R1Z.PV_Inv_MaskTail57
import R1Z.PV_Inv_MaskTail58
import R1Z.PV_Inv_MaskTail59
import R1Z.PV_Inv_MaskTail60
import R1Z.PV_Inv_MaskTail61
import R1Z.PV_Inv_MaskTail62
import R1Z.PV_Inv_MaskTail63
set_option autoImplicit false
namespace R1Z.PV_Inv_MaskTail
open R0P

theorem source_equation (block : Fin 64) (tail : 48 ≤ block.val) :
    PV_Inv_MaskSource.mask block = copyActiveRowMasks block := by
  rcases block with ⟨b,hb⟩
  interval_cases b <;> first
  | exact PV_Inv_MaskTail48.block
  | exact PV_Inv_MaskTail49.block
  | exact PV_Inv_MaskTail50.block
  | exact PV_Inv_MaskTail51.block
  | exact PV_Inv_MaskTail52.block
  | exact PV_Inv_MaskTail53.block
  | exact PV_Inv_MaskTail54.block
  | exact PV_Inv_MaskTail55.block
  | exact PV_Inv_MaskTail56.block
  | exact PV_Inv_MaskTail57.block
  | exact PV_Inv_MaskTail58.block
  | exact PV_Inv_MaskTail59.block
  | exact PV_Inv_MaskTail60.block
  | exact PV_Inv_MaskTail61.block
  | exact PV_Inv_MaskTail62.block
  | exact PV_Inv_MaskTail63.block
  | omega

#print axioms source_equation
end R1Z.PV_Inv_MaskTail
