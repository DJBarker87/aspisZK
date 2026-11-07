import NMO_ClaimsAtState
import NMC_AllSlotFrames
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_ExtraValue
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
def Canonical (words : Words) : Prop := ∀ q∈words.val,JFv_RoundArithmetic.Canonical q
/-- Decoder147 produces only canonical successful words, even before any
parser provenance is used. Rejections and aborts are not turned into success. -/
theorem decoded (record : r1_wire.ValidatedRecord) (offset : Usize) (out : Words)
 (returned : NJM_RoundJoin.R.decode 29#usize record offset=ok (.Ok out)) : Canonical out := by
 have all:=JFv_DecodeCanonical.source record offset out returned
 intro q member
 obtain ⟨i,hi,same⟩:=List.mem_iff_getElem.mp member
 have bound : i<29 := by have len:=out.property;change out.val.length=29 at len;omega
 have canonical:=all ⟨i,bound⟩
 rw [←same]
 exact canonical
#print axioms decoded
end AspisR1.NMO_ExtraValue
end
