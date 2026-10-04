import AspisR614SelectedCombineBeta.Funs
import AspisV8R19.GeneratedInverseLoop
import AspisV8R19.InverseRuntimeMul

set_option autoImplicit false
namespace AspisV8R19.R624DecoderInnerExecution

open Aeneas Aeneas.Std Result ControlFlow Error

abbrev DecoderIter := core.ops.range.Range Std.Usize
abbrev DecoderPending (N : Std.Usize) := DecoderIter × Array Std.U32 N × Std.U32
abbrev DecoderDone (N : Std.Usize) := Array Std.U32 N × Std.U32

def sourceMaskCast (w : Std.U64) : Result Std.U32 := do
  let i1 ← lift (core.convert.num.FromU64U32.from 2147483647#u32)
  let i2 ← lift (w &&& i1)
  lift (UScalar.cast .U32 i2)

/-- The exact generated inner-loop operations after `IteratorRange.next` has
returned an index.  The result keeps every checked failure from indexing,
casting, and array update, and keeps the source's wrapping operations. -/
def wordStep {N : Std.Usize} (block : Std.Usize)
    (v : Array Std.U64 8#usize) (j : Std.Usize)
    (out : Array Std.U32 N) (invalid : Std.U32) : Result (DecoderDone N) := do
  let i ← Array.index_usize v j
  let value ← sourceMaskCast i
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

theorem wordRun_zero {N : Std.Usize} (block : Std.Usize) (v : Array Std.U64 8#usize)
    (iter : DecoderIter) (out : Array Std.U32 N) (invalid : Std.U32) :
    wordRun block v 0 iter out invalid = .ok (out, invalid) := rfl

/-- The generated body is exactly iterator advancement followed by `wordStep`.
This equality deliberately retains the iterator exhaustion branch. -/
theorem body_factor {N : Std.Usize} (block : Std.Usize)
    (v : Array Std.U64 8#usize) (iter : DecoderIter)
    (out : Array Std.U32 N) (invalid : Std.U32) :
    AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into_loop0_loop0.body
      block v iter out invalid =
      (do
        let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
        match o with
        | none => ok (.done (out, invalid))
        | some j => do
            let (out1, invalid1) ← wordStep block v j out invalid
            ok (.cont (iter1, out1, invalid1))) := by
  simp only [AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into_loop0_loop0.body,
    wordStep, sourceMaskCast, bind_assoc, bind_tc_ok, lift]
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
      simp only [Prod.fst, Prod.snd]
      rw [body_factor block v iter out invalid]
      rw [AspisV8R19.GeneratedInverseLoop.range_next]
      simp only [dif_pos hlt, bind_tc_ok]
      rw [wordRun]
      rw [AspisV8R19.GeneratedInverseLoop.range_next]
      simp only [dif_pos hlt, bind_tc_ok]
      cases hs : wordStep block v iter.start out invalid with
      | fail e => simp [hs]
      | div => simp [hs]
      | ok pair =>
          rcases pair with ⟨out1, invalid1⟩
          simp only [hs, bind_tc_ok]
          simpa only [AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into_loop0_loop0] using
            (ih iter1 out1 invalid1 hn1)

/-- The scalar value produced by the source's U64 mask and U32 cast. -/
def sourceMaskedValue (w : Std.U64) : Std.U32 :=
  UScalar.cast .U32 (UScalar.and w (UScalar.cast .U64 (2147483647#u32)))

theorem sourceMaskedValue_bound (w : Std.U64) :
    (sourceMaskedValue w).val ≤ 2147483647 := by
  have hand : (UScalar.and w (UScalar.cast .U64 (2147483647#u32))).val =
      w.val &&& 2147483647 := by
    rw [AspisV8R19.InverseRuntimeMul.and_value,
      AspisV8R19.InverseRuntimeMul.cast_widen_value]
    norm_num
  have hmask : w.val &&& 2147483647 ≤ 2147483647 :=
    Nat.and_le_right
  have hlt : (UScalar.and w (UScalar.cast .U64 (2147483647#u32))).val < 2^32 := by
    rw [hand]
    omega
  rw [sourceMaskedValue, AspisV8R19.InverseRuntimeMul.narrow_exact _ hlt, hand]
  exact hmask

theorem sourceMaskCast_exact (w : Std.U64) :
    sourceMaskCast w = .ok (sourceMaskedValue w) := by
  simp only [sourceMaskCast, sourceMaskedValue,
    core.convert.num.FromU64U32.from, bind_tc_ok, lift,
    UScalar.and, UScalar.cast]
  rfl

/-- Nat-indexed representation of the single in-range output write. -/
def setNat {N : Std.Usize} (out : Array Std.U32 N) (k : Nat) (x : Std.U32) :
    Array Std.U32 N :=
  ⟨out.val.set k x, by simpa only [List.length_set] using out.property⟩

def sourceWord (v : Array Std.U64 8#usize) (j : Std.Usize)
    (hj : j.val < 8) : Std.U64 :=
  v.val[j.val]'(by have hv : v.val.length = 8 := v.property; omega)

def sourceOutputIndex (block j : Std.Usize) : Nat := 8 * block.val + j.val

def sourceInvalid (invalid value : Std.U32) : Std.U32 :=
  UScalar.or invalid (Std.U32.wrapping_add value 1#u32)

theorem source_index_success (v : Array Std.U64 8#usize) (j : Std.Usize)
    (hj : j.val < 8) :
    Array.index_usize v j = .ok (sourceWord v j hj) := by
  have hv : v.val.length = 8 := v.property
  simp [Array.index_usize, sourceWord, Array.getElem?_eq_getElem, hv, hj]

theorem source_update_success {N : Std.Usize} (out : Array Std.U32 N)
    (i : Std.Usize) (x : Std.U32) (hi : i.val < N.val) :
    Array.update out i x = .ok (setNat out i.val x) := by
  have hout : out.val.length = N.val := out.property
  simp [Array.update, setNat, Array.getElem?_eq_getElem, hout, hi]

theorem source_index_arithmetic {N : Std.Usize} (block j : Std.Usize)
    (hindex : 8 * block.val + j.val < N.val) :
    (Std.Usize.wrapping_add (Std.Usize.wrapping_mul 8#usize block) j).val =
      sourceOutputIndex block j := by
  have hN : N.val < UScalar.size .Usize := by
    simpa [UScalar.size, UScalarTy.numBits, Usize.size, Usize.numBits] using N.bv.isLt
  have hproduct : 8 * block.val < UScalar.size .Usize := by omega
  have hsum : 8 * block.val + j.val < UScalar.size .Usize := by omega
  have hmul : (Std.Usize.wrapping_mul 8#usize block).val = 8 * block.val := by
    rw [Std.Usize.wrapping_mul_val_eq]
    exact Nat.mod_eq_of_lt hproduct
  rw [Std.Usize.wrapping_add_val_eq, hmul]
  simp only [sourceOutputIndex]
  exact Nat.mod_eq_of_lt hsum

def sourceWordNat (v : Array Std.U64 8#usize) (i : Nat)
    (hi : i < 8) : Std.U64 :=
  v.val[i]'(by have hv : v.val.length = 8 := v.property; omega)

/-- The exact eight-position update/invalid fold.  Each `setNat` is justified
by the complete block bound; the recursive index order is the source order. -/
def blockAcc {N : Std.Usize} (block : Std.Usize)
    (v : Array Std.U64 8#usize)
    (hblock : 8 * (block.val + 1) ≤ N.val) :
    (start n : Nat) → start + n ≤ 8 → Array Std.U32 N → Std.U32 →
      Array Std.U32 N × Std.U32
  | start, 0, _, out, invalid => (out, invalid)
  | start, n + 1, hlen, out, invalid =>
      let value := sourceMaskedValue (sourceWordNat v start (by omega))
      let out1 := setNat out (8 * block.val + start) value
      blockAcc block v hblock (start + 1) n (by omega) out1
        (sourceInvalid invalid value)
termination_by start n _ _ _ => n


/-- Exact successful post-iterator word step.  The hypotheses are exactly the
source word-array bound and output-array bound; no source index or update
success is assumed. -/
theorem wordStep_success {N : Std.Usize} (block : Std.Usize)
    (v : Array Std.U64 8#usize) (j : Std.Usize)
    (out : Array Std.U32 N) (invalid : Std.U32)
    (hj : j.val < 8)
    (hindex : sourceOutputIndex block j < N.val) :
    wordStep block v j out invalid =
      .ok (setNat out (sourceOutputIndex block j)
        (sourceMaskedValue (sourceWord v j hj)),
        sourceInvalid invalid (sourceMaskedValue (sourceWord v j hj))) := by
  have hstepidx := source_index_arithmetic (N := N) block j hindex
  have hwrite : (Std.Usize.wrapping_add (Std.Usize.wrapping_mul 8#usize block) j).val < N.val := by
    rw [hstepidx]
    exact hindex
  simp only [wordStep, source_index_success v j hj, sourceMaskCast_exact, bind_tc_ok, lift]
  rw [source_update_success out _ _ hwrite]
  simp only [bind_tc_ok]
  rw [hstepidx]
  unfold sourceInvalid
  rfl

theorem wordRun_block {N : Std.Usize} (block : Std.Usize)
    (v : Array Std.U64 8#usize)
    (hblock : 8 * (block.val + 1) ≤ N.val)
    (start n : Nat) (iter : DecoderIter) (out : Array Std.U32 N)
    (invalid : Std.U32)
    (hlen : iter.end.val - iter.start.val = n)
    (hstart : iter.start.val = start) (hwithin : start + n ≤ 8) :
    wordRun block v n iter out invalid =
      .ok (blockAcc block v hblock start n hwithin out invalid) := by
  induction n generalizing start iter out invalid with
  | zero =>
      simp [wordRun, blockAcc]
  | succ n ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      have hword : iter.start.val < 8 := by omega
      have hidx : sourceOutputIndex block iter.start < N.val := by
        rw [sourceOutputIndex]
        have := hblock
        have hs := hstart
        omega
      let iter1 : DecoderIter :=
        { start := UScalar.ofNatCore (iter.start.val + 1)
            (by have := iter.end.hBounds; omega), «end» := iter.end }
      have hlen1 : iter1.end.val - iter1.start.val = n := by
        change iter.end.val - (iter.start.val + 1) = n
        omega
      have hstart1 : iter1.start.val = start + 1 := by
        simp [iter1, hstart]
      have hwithin1 : (start + 1) + n ≤ 8 := by omega
      rw [wordRun]
      rw [AspisV8R19.GeneratedInverseLoop.range_next]
      simp only [dif_pos hlt, bind_tc_ok]
      rw [wordStep_success block v iter.start out invalid hword hidx]
      simp only [bind_tc_ok]
      rw [ih (start + 1) iter1
        (setNat out (sourceOutputIndex block iter.start)
          (sourceMaskedValue (sourceWord v iter.start hword)))
        (sourceInvalid invalid (sourceMaskedValue (sourceWord v iter.start hword)))
        hlen1 hstart1 hwithin1]
      simp [blockAcc, hstart, sourceOutputIndex, sourceWord, sourceWordNat]


/-- Eight-index instance used by the captured decoder. -/
theorem loop_exec_eight {N : Std.Usize} (block : Std.Usize)
    (v : Array Std.U64 8#usize) (out : Array Std.U32 N) (invalid : Std.U32) :
    AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into_loop0_loop0
      { start := 0#usize, «end» := 8#usize } out invalid block v =
      wordRun block v 8 { start := 0#usize, «end» := 8#usize } out invalid := by
  apply loop_exec
  simp

#print axioms sourceMaskedValue_bound
#print axioms source_index_success
#print axioms source_update_success
#print axioms source_index_arithmetic
#print axioms wordStep_success
#print axioms blockAcc
#print axioms wordRun_block
#print axioms sourceMaskCast_exact
#print axioms wordStep
#print axioms wordRun
#print axioms body_factor
#print axioms loop_exec
#print axioms loop_exec_eight

end AspisV8R19.R624DecoderInnerExecution
