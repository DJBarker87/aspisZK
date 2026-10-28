import NDO_JGi_FieldCell
import NDO_JGi_FieldWindows
set_option autoImplicit false
namespace AspisR1.JGi_Y1Cell28
open Aeneas Aeneas.Std Result AspisR1CurrentPreparedClaim
open AspisR1.ExtractedRecordByteCanonicality
def arr : Array U8 32#usize := Array.make 32#usize [132#u8,34#u8,205#u8,24#u8,61#u8,12#u8,127#u8,6#u8,218#u8,51#u8,141#u8,7#u8,13#u8,180#u8,50#u8,85#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem selected : (JGe_Payload27.value.val.drop (32*28)).take 32=arr.val := by
  rw [JGi_FieldWindows.selected 28 (by decide)]
  rfl
#print axioms selected
theorem word0 : wordLE arr 0=416096900#u32 := by rfl
#print axioms word0
theorem word1 : wordLE arr 1=108989501#u32 := by rfl
#print axioms word1
theorem word2 : wordLE arr 2=126694362#u32 := by rfl
#print axioms word2
theorem word3 : wordLE arr 3=1429386253#u32 := by rfl
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
theorem source : ∃ out,ClaimParser.field JGe_Payload27.value 28#usize=ok out ∧ Concrete.Canonical out := by
  exact JGi_FieldCell.source _ _ arr (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) selected bounds
#print axioms source
end AspisR1.JGi_Y1Cell28
