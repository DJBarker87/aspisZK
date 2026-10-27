import R1Z.ProverRw21FlatLimbs
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21FlatSourceLaw
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw21ArrayRead ProverRw21FlatOutput

theorem exact (x : W) : ProverRwP6FlatSource.wide_bytes_flat x=ok (output x) := by
  unfold ProverRwP6FlatSource.wide_bytes_flat
    ProverRwP6FlatSource.aspis_core.field.wide_exact.WideExact.to_limbs
    ProverRwDictionaryBytes.Src.limbs
    ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.to_limbs
  simp only [bind_tc_ok]
  have hw0 := ProverRw21FlatLimbs.word0 x
  dsimp only [words] at hw0
  rw [hw0]
  simp only [bind_tc_ok,lift]
  have hw1 := ProverRw21FlatLimbs.word1 x
  dsimp only [words] at hw1
  rw [hw1]
  simp only [bind_tc_ok,lift]
  have hw2 := ProverRw21FlatLimbs.word2 x
  dsimp only [words] at hw2
  rw [hw2]
  simp only [bind_tc_ok,lift]
  have hw3 := ProverRw21FlatLimbs.word3 x
  dsimp only [words] at hw3
  rw [hw3]
  simp only [bind_tc_ok,lift]
  have hw4 := ProverRw21FlatLimbs.word4 x
  dsimp only [words] at hw4
  rw [hw4]
  simp only [bind_tc_ok,lift]
  have hw5 := ProverRw21FlatLimbs.word5 x
  dsimp only [words] at hw5
  rw [hw5]
  simp only [bind_tc_ok,lift]
  have hw6 := ProverRw21FlatLimbs.word6 x
  dsimp only [words] at hw6
  rw [hw6]
  simp only [bind_tc_ok,lift]
  have hw7 := ProverRw21FlatLimbs.word7 x
  dsimp only [words] at hw7
  rw [hw7]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c0.a) 0#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c0.a) 1#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c0.a) 2#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c0.a) 3#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c0.b) 0#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c0.b) 1#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c0.b) 2#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c0.b) 3#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c1.a) 0#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c1.a) 1#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c1.a) 2#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c1.a) 3#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c1.b) 0#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c1.b) 1#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c1.b) 2#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c0.c1.b) 3#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c0.a) 0#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c0.a) 1#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c0.a) 2#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c0.a) 3#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c0.b) 0#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c0.b) 1#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c0.b) 2#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c0.b) 3#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c1.a) 0#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c1.a) 1#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c1.a) 2#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c1.a) 3#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c1.b) 0#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c1.b) 1#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c1.b) 2#usize (by decide)]
  simp only [bind_tc_ok,lift]
  rw [exact_read (core.num.U32.to_le_bytes x.c1.c1.b) 3#usize (by decide)]
  simp only [bind_tc_ok,lift]
  apply congrArg Result.ok
  apply Subtype.ext
  change _=bytes x
  unfold bytes
  rw [four (core.num.U32.to_le_bytes x.c0.c0.a)]
  rw [four (core.num.U32.to_le_bytes x.c0.c0.b)]
  rw [four (core.num.U32.to_le_bytes x.c0.c1.a)]
  rw [four (core.num.U32.to_le_bytes x.c0.c1.b)]
  rw [four (core.num.U32.to_le_bytes x.c1.c0.a)]
  rw [four (core.num.U32.to_le_bytes x.c1.c0.b)]
  rw [four (core.num.U32.to_le_bytes x.c1.c1.a)]
  rw [four (core.num.U32.to_le_bytes x.c1.c1.b)]
  rfl

#print axioms exact
end R1Z.ProverRw21FlatSourceLaw
