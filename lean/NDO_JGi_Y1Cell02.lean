import NDO_JGi_FieldCell
import NDO_JGi_FieldWindows
set_option autoImplicit false
namespace AspisR1.JGi_Y1Cell02
open Aeneas Aeneas.Std Result AspisR1CurrentPreparedClaim
open AspisR1.ExtractedRecordByteCanonicality
def arr : Array U8 32#usize := Array.make 32#usize [148#u8,62#u8,130#u8,121#u8,55#u8,9#u8,143#u8,40#u8,145#u8,201#u8,103#u8,29#u8,96#u8,88#u8,145#u8,24#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem selected : (JGe_Payload27.value.val.drop (32*2)).take 32=arr.val := by
  rw [JGi_FieldWindows.selected 2 (by decide)]
  rfl
#print axioms selected
theorem word0 : wordLE arr 0=2038578836#u32 := by rfl
#print axioms word0
theorem word1 : wordLE arr 1=680462647#u32 := by rfl
#print axioms word1
theorem word2 : wordLE arr 2=493341073#u32 := by rfl
#print axioms word2
theorem word3 : wordLE arr 3=412178528#u32 := by rfl
#print axioms word3
theorem word4 : wordLE arr 4=0#u32 := by rfl
#print axioms word4
theorem word5 : wordLE arr 5=0#u32 := by rfl
#print axioms word5
theorem word6 : wordLE arr 6=0#u32 := by rfl
#print axioms word6
theorem word7 : wordLE arr 7=0#u32 := by rfl
#print axioms word7
theorem bounds : ∀ j : Fin 8,(wordLE arr j).val<2147483647 := by
  intro j
  fin_cases j
  · change (wordLE arr 0).val<2147483647
    rw [word0];scalar_tac
  · change (wordLE arr 1).val<2147483647
    rw [word1];scalar_tac
  · change (wordLE arr 2).val<2147483647
    rw [word2];scalar_tac
  · change (wordLE arr 3).val<2147483647
    rw [word3];scalar_tac
  · change (wordLE arr 4).val<2147483647
    rw [word4];scalar_tac
  · change (wordLE arr 5).val<2147483647
    rw [word5];scalar_tac
  · change (wordLE arr 6).val<2147483647
    rw [word6];scalar_tac
  · change (wordLE arr 7).val<2147483647
    rw [word7];scalar_tac
#print axioms bounds
theorem source : ∃ out,ClaimParser.field JGe_Payload27.value 2#usize=ok out ∧ Concrete.Canonical out := by
  exact JGi_FieldCell.source _ _ arr (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) selected bounds
#print axioms source
end AspisR1.JGi_Y1Cell02
