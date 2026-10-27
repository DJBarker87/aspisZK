import LPt_LPl_G_Scanners
import LPt_LPl_C_TailTransport
open Aeneas Aeneas.Std Result LPt_LPl_Kit_Release
set_option autoImplicit false
namespace LPt_LPl.Echeck
/-- Value port used by the native little-endian polynomial gate. -/
def byte (bs : List U8) (i : Nat) : Nat := (bs[i]?.getD 0#u8).val
def word (bs : List U8) : Nat :=
  byte bs 0 + 256 * (byte bs 1 + 256 * (byte bs 2 + 256 * byte bs 3))
/-- Exact local decoder specification; all bytes, including rejected words. -/
def chunk (bs : List U8) (k : Bool) : Bool :=
  (List.range 8).all fun j =>
    let n := word ((bs.drop (4*j)).take 4)
    decide (n < 2147483647) && (!k || decide (j < 4 ∨ n = 0))

theorem word_eq_le32 (bs : List U8) : word bs = LPt_LPl_Kit_Bytes.le32 bs := by
  rcases bs with _ | ⟨a,bs⟩ <;>
    first | rfl | skip
  rcases bs with _ | ⟨b,bs⟩ <;>
    first | simp [word, byte, LPt_LPl_Kit_Bytes.le32] | skip
  rcases bs with _ | ⟨c,bs⟩ <;>
    first | simp [word, byte, LPt_LPl_Kit_Bytes.le32] | skip
  rcases bs with _ | ⟨d,bs⟩ <;>
    simp [word, byte, LPt_LPl_Kit_Bytes.le32]

theorem chunk_eq (bs : List U8) (k : Bool) :
    chunk bs k = LPt_LPl_Kit_Bytes.validChunk 8 k bs := by
  simp only [chunk, LPt_LPl_Kit_Bytes.validChunk, word_eq_le32]

/-- The pointer-selected native window is the SAME list window consumed by the model. -/
theorem window (bs : List U8) (i : Nat) (native : List U8)
    (pointerWindow : native = (bs.drop (32*i)).take 32) (k : Bool) :
    chunk native k = LPt_LPl_A.Echeck.predicate bs k i := by
  rw [pointerWindow, chunk_eq]
  rfl

#print axioms word_eq_le32
#print axioms chunk_eq
#print axioms window
end LPt_LPl.Echeck
