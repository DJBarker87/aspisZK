import NBP_DigestEncode
import NBG_Utilities
set_option autoImplicit false
noncomputable section
namespace NBP_DigestLayout
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open AspisR1.S2K
/-- The recursive exact model result has the ordered four-byte word layout. -/
theorem bytes (digest : Array U32 8#usize) :
    (DigestBytes.bytes digest).val =
      digest.val.flatMap (fun w => (core.num.U32.to_le_bytes w).val) := by
  obtain ⟨a,b,c,d,e,f,g,h,same⟩ := NBG_Utilities.shape digest
  subst digest
  simp [DigestBytes.bytes,DigestBytes.fold,NBG_Utilities.pack,
    Array.make,Array.repeat,Array.setSlice!,core.num.U32.to_le_bytes,
    BitVec.toLEBytes,List.setSlice!,List.slice]
#print axioms bytes
end NBP_DigestLayout
