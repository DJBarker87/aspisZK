import R1Z.ProverRw18ComplexRegion
set_option autoImplicit false
namespace R1Z.ProverRw18QuarticWrite
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Q := aspis_core.field.QM31
abbrev source := ProverRwDictionaryBytesSource.aspis_core.field.QM31.write_le_bytes

def output (x : Q) (out : Slice U8) : Slice U8 :=
  ProverRw18ComplexRegion.output x.c1 (ProverRw18ComplexRegion.output x.c0 out 0#usize) 8#usize

theorem context (x : Q) (out : Slice U8) : source x out=(do
    let first ← ProverRw18ComplexRegion.write x.c0 out 0#usize 8#usize
    ProverRw18ComplexRegion.write x.c1 first 8#usize 16#usize) := by
  simp only [source,ProverRwDictionaryBytesSource.aspis_core.field.QM31.write_le_bytes,
    ProverRw18ComplexRegion.write,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
  cases first : core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8) out ⟨0#usize,8#usize⟩ with
  | fail error => rfl
  | div => rfl
  | ok pair => rcases pair with ⟨segment,back⟩;rfl

theorem exact_write (x : Q) (out : Slice U8) (bound : 16≤out.val.length) :
    source x out=ok (output x out) := by
  rw [context,ProverRw18ComplexRegion.exact_write]
  · simp only [bind_tc_ok]
    rw [ProverRw18ComplexRegion.exact_write]
    · rfl
    · decide
    · simp only [ProverRw18ComplexRegion.output,List.length_setSlice!]
      change 16≤out.val.length
      exact bound
    · decide
  · decide
  · change 8≤out.val.length
    omega
  · decide

#print axioms context
#print axioms exact_write
end R1Z.ProverRw18QuarticWrite
