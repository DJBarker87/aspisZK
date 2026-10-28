import NCO_Word
import LPr_WordNat
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_WordNat

theorem value (a b c d : U8) :
    (NCO_Word.packed a b c d).val =
      a.val + 256 * (b.val + 256 * (c.val + 256 * d.val)) := by
  have same : NCO_Word.packed a b c d =
      core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d]) :=
    Result.ok.inj ((NCO_Word.word_packed a b c d).symm.trans (NCO_Word.little_endian a b c d))
  rw [same, AspisR1.LPr_WordNat.value]
  omega

#print axioms value
end NCO_WordNat
