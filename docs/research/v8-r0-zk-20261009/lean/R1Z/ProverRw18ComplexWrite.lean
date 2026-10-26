import R1Z.ProverRw18SliceWrite
import R1Z.ProverRwDictionaryBytesSource
set_option autoImplicit false
namespace R1Z.ProverRw18ComplexWrite
open Aeneas Aeneas.Std Result ProverRwFull
abbrev C := aspis_core.field.CM31
abbrev source := ProverRwDictionaryBytesSource.aspis_core.field.CM31.write_le_bytes

def word (x : U32) : Slice U8 := Array.to_slice (core.num.U32.to_le_bytes x)
def output (x : C) (out : Slice U8) : Slice U8 :=
  ProverRw18SliceWrite.put (ProverRw18SliceWrite.put out 0#usize (word x.a)) 4#usize (word x.b)

theorem context (x : C) (out : Slice U8) : source x out=(do
    let first ← ProverRw18SliceWrite.write out 0#usize 4#usize (word x.a)
    ProverRw18SliceWrite.write first 4#usize 8#usize (word x.b)) := by
  simp only [source,ProverRwDictionaryBytesSource.aspis_core.field.CM31.write_le_bytes,
    ProverRwDictionaryBytesSource.aspis_core.field.M31.to_le_bytes,
    ProverRw18SliceWrite.write,word,lift,bind_tc_ok,bind_assoc_eq,Aeneas.Std.uncurry]
  cases first : core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8) out ⟨0#usize,4#usize⟩ with
  | fail error => rfl
  | div => rfl
  | ok pair => rcases pair with ⟨segment,back⟩; rfl

theorem word_length (x : U32) : (word x).val.length=4 :=
  (core.num.U32.to_le_bytes x).property

theorem exact_write (x : C) (out : Slice U8) (bound : 8≤out.val.length) :
    source x out=ok (output x out) := by
  rw [context,ProverRw18SliceWrite.exact_write]
  · simp only [bind_tc_ok]
    rw [ProverRw18SliceWrite.exact_write]
    · rfl
    · decide
    · simp only [ProverRw18SliceWrite.put,List.length_setSlice!]
      change 8≤out.val.length
      exact bound
    · exact (word_length x.b).symm
  · decide
  · exact Nat.le_trans (by decide) bound
  · exact (word_length x.a).symm

#print axioms context
#print axioms word_length
#print axioms exact_write
end R1Z.ProverRw18ComplexWrite
