import LPr_WordValue
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_Word

def packed (a b c d : U8) : U32 :=
  ⟨(BitVec.zeroExtend 32 a.bv) ||| ((BitVec.zeroExtend 32 b.bv) <<< 8) |||
    ((BitVec.zeroExtend 32 c.bv) <<< 16) ||| ((BitVec.zeroExtend 32 d.bv) <<< 24)⟩

def word (a b c d : U8) : Result U32 := do
  let b1 ← (UScalar.cast .U32 b) <<< 8#i32
  let c1 ← (UScalar.cast .U32 c) <<< 16#i32
  let d1 ← (UScalar.cast .U32 d) <<< 24#i32
  ok ((UScalar.cast .U32 a) ||| b1 ||| c1 ||| d1)

theorem word_packed (a b c d : U8) : word a b c d = ok (packed a b c d) := by
  rfl

theorem bits (a b c d : U8) :
    (packed a b c d).bv = d.bv ++ c.bv ++ b.bv ++ a.bv := by
  have h := BitVec.setWidth_append_append_append_eq_shiftLeft_setWidth_or
    (w'''' := 32) (b := d.bv) (b' := c.bv) (b'' := b.bv) (b''' := a.bv)
  simpa only [packed, BitVec.setWidth_eq, BitVec.or_comm,
    BitVec.or_assoc] using h.symm

theorem little_endian (a b c d : U8) :
    word a b c d = ok (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])) := by
  rw [word_packed]
  have h : (packed a b c d).bv =
      (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).bv := by
    rw [AspisR1.LPr_WordValue.bits]
    exact bits a b c d
  exact congrArg ok (congrArg (fun bv : BitVec 32 => (⟨bv⟩ : U32)) h)

#print axioms word_packed
#print axioms bits
#print axioms little_endian
end NCO_Word
