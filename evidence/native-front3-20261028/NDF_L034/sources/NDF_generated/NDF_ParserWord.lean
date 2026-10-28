import NCO_Word
set_option autoImplicit false
namespace NDF_ParserWord
open Aeneas Aeneas.Std Result

def packed (a b c d : U8) : Usize :=
  ⟨(BitVec.zeroExtend 64 a.bv) ||| ((BitVec.zeroExtend 64 b.bv) <<< 8) |||
    ((BitVec.zeroExtend 64 c.bv) <<< 16) ||| ((BitVec.zeroExtend 64 d.bv) <<< 24)⟩

def word (a b c d : U8) : Result Usize := do
  let b1 ← (UScalar.cast .Usize b) <<< 8#i32
  let c1 ← (UScalar.cast .Usize c) <<< 16#i32
  let d1 ← (UScalar.cast .Usize d) <<< 24#i32
  ok ((UScalar.cast .Usize a) ||| b1 ||| c1 ||| d1)

theorem word_packed (a b c d : U8) : word a b c d=ok (packed a b c d) := rfl

theorem bits (a b c d : U8) :
    (packed a b c d).bv = (d.bv ++ c.bv ++ b.bv ++ a.bv).setWidth 64 := by
  have h := BitVec.setWidth_append_append_append_eq_shiftLeft_setWidth_or
    (w'''' := 64) (b := d.bv) (b' := c.bv) (b'' := b.bv) (b''' := a.bv)
  simpa only [packed,BitVec.setWidth_eq,BitVec.or_comm,BitVec.or_assoc] using h.symm

theorem little_endian (a b c d : U8) :
    word a b c d=ok (UScalar.cast .Usize (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d]))) := by
  rw [word_packed]
  congr 1
  apply UScalar.eq_of_bv_eq
  change (packed a b c d).bv = (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).bv.setWidth 64
  rw [AspisR1.LPr_WordValue.bits]
  exact bits a b c d

#print axioms word_packed
#print axioms bits
#print axioms little_endian
end NDF_ParserWord
