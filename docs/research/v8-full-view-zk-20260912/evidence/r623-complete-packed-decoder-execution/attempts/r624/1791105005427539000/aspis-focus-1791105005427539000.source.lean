import AspisR614SelectedCombineBeta.Funs
import AspisV8R19.GeneratedInverseLoop

set_option autoImplicit false
namespace AspisV8R19.R624DecoderInnerExecution

open Aeneas Aeneas.Std Result ControlFlow Error

abbrev DecoderIter := core.ops.range.Range Std.Usize
abbrev DecoderPending (N : Std.Usize) := DecoderIter × Array Std.U32 N × Std.U32
abbrev DecoderDone (N : Std.Usize) := Array Std.U32 N × Std.U32

/-- The exact generated inner-loop operations after `IteratorRange.next` has
returned an index.  The result keeps every checked failure from indexing,
casting, and array update, and keeps the source's wrapping operations. -/
def wordStep {N : Std.Usize} (block : Std.Usize)
    (v : Array Std.U64 8#usize) (j : Std.Usize)
    (out : Array Std.U32 N) (invalid : Std.U32) : Result (DecoderDone N) := do
  let i ← Array.index_usize v j
  let i1 ← lift (core.convert.num.FromU64U32.from 2147483647#u32)
  let i2 ← lift (i &&& i1)
  let value ← lift (UScalar.cast .U32 i2)
  let i3 ← lift (Std.Usize.wrapping_mul 8#usize block)
  let i4 ← lift (Std.Usize.wrapping_add i3 j)
  let a ← Array.update out i4 value
  let i5 ← lift (Std.U32.wrapping_add value 1#u32)
  let invalid1 ← lift (invalid ||| i5)
  ok (a, invalid1)

/-- Nat-bounded execution model.  It performs the same iterator `next` and
then delegates exactly the post-`next` operations to `wordStep`. -/
def wordRun {N : Std.Usize} (block : Std.Usize)
    (v : Array Std.U64 8#usize) : Nat → DecoderIter → Array Std.U32 N → Std.U32 →
      Result (DecoderDone N)
  | 0, _, out, invalid => ok (out, invalid)
  | n + 1, iter, out, invalid => do
      let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok (out, invalid)
      | some j => do
          let (out1, invalid1) ← wordStep block v j out invalid
          wordRun block v n iter1 out1 invalid1

theorem wordRun_zero (block : Std.Usize) (v : Array Std.U64 8#usize)
    (iter : DecoderIter) (out : Array Std.U32 N) (invalid : Std.U32) :
    wordRun block v 0 iter out invalid = .ok (out, invalid) := rfl

/-- The generated body is exactly iterator advancement followed by `wordStep`.
This equality deliberately retains the iterator exhaustion branch. -/
theorem body_factor {N : Std.Usize} (block : Std.Usize)
    (v : Array Std.U64 8#usize) (iter : DecoderIter)
    (out : Array Std.U32 N) (invalid : Std.U32) :
    AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into_loop0_loop0.body
      block v iter out invalid = do
        let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
        match o with
        | none => ok (.done (out, invalid))
        | some j => do
            let (out1, invalid1) ← wordStep block v j out invalid
            ok (.cont (iter1, out1, invalid1)) := by
  simp only [AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into_loop0_loop0.body,
    wordStep, bind_assoc, bind_tc_ok, lift]
  rfl

/-- The actual generated loop equals `wordRun` for the exact number of
indices remaining in any Usize range.  All source errors and the advanced
output array are preserved. -/
theorem loop_exec {N : Std.Usize} (block : Std.Usize)
    (v : Array Std.U64 8#usize) (iter : DecoderIter)
    (out : Array Std.U32 N) (invalid : Std.U32)
    (n : Nat) (hn : iter.end.val - iter.start.val = n) :
    AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into_loop0_loop0
      iter out invalid block v = wordRun block v n iter out invalid := by
  induction n generalizing iter out invalid with
  | zero =>
      have hstop : ¬ iter.start.val < iter.end.val := by omega
      rw [AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into_loop0_loop0,
        loop.eq_def]
      have hbody :
          AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into_loop0_loop0.body
            block v iter out invalid = .ok (.done (out, invalid)) := by
        rw [body_factor]
        rw [AspisV8R19.GeneratedInverseLoop.range_next]
        simp [hstop]
      simp only [hbody, wordRun]
  | succ n ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      let iter1 : DecoderIter :=
        { start := UScalar.ofNatCore (iter.start.val + 1)
            (by have := iter.end.hBounds; omega), «end» := iter.end }
      have hn1 : iter1.end.val - iter1.start.val = n := by
        change iter.end.val - (iter.start.val + 1) = n
        omega
      rw [AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into_loop0_loop0,
        loop.eq_def]
      have hbody :
          AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into_loop0_loop0.body
            block v iter out invalid = do
              let (out1, invalid1) ← wordStep block v iter.start out invalid
              ok (.cont (iter1, out1, invalid1)) := by
        rw [body_factor, AspisV8R19.GeneratedInverseLoop.range_next]
        simp only [dif_pos hlt, bind_tc_ok]
        rfl
      rw [hbody]
      simp only [bind_tc_ok]
      rw [ih iter1 out invalid hn1]
      simp [wordRun, AspisV8R19.GeneratedInverseLoop.range_next, hlt,
        bind_tc_ok, iter1]

/-- Eight-index instance used by the captured decoder. -/
theorem loop_exec_eight {N : Std.Usize} (block : Std.Usize)
    (v : Array Std.U64 8#usize) (out : Array Std.U32 N) (invalid : Std.U32) :
    AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into_loop0_loop0
      { start := 0#usize, «end» := 8#usize } out invalid block v =
      wordRun block v 8 { start := 0#usize, «end» := 8#usize } out invalid := by
  apply loop_exec
  simp

#print axioms wordStep
#print axioms wordRun
#print axioms body_factor
#print axioms loop_exec
#print axioms loop_exec_eight

end AspisV8R19.R624DecoderInnerExecution
