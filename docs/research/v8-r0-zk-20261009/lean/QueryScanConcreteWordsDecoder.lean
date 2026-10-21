import TerminalArrayFromFnModelV4Clean
import TerminalStandardOperationModelsV1
import SelectorArrayMapSuccess
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace AspisR1QueryScanUnrolled

/-- Exact operation aliases from the checked, axiom-free Aeneas standard-operation owner. -/
def core.array.from_fn {T F : Type} (N : Usize)
    (callback : core.ops.function.FnMut F Usize T) (f : F) : Result (Array T N) :=
  AspisR1SelectedMaskProbe.core.array.from_fn N callback f

def core.array.Array.map {T F U : Type} {N : Usize}
    (callback : core.ops.function.FnMut F T U) (a : Array T N) (f : F) :
    Result (Array U N) :=
  AspisR1SelectedMaskProbe.core.array.Array.map callback a f

/-- Source constants from r0_transcript.rs. -/
def r0_transcript.QUERY_BOUND : Result Std.U32 := 1#u32 <<< 18#i32

def r0_transcript.block_rank.closure := Array Std.U8 32#usize
def r0_transcript.query_words.closure := Unit

/-- Exact extracted `block_rank` callback body: four checked byte reads and LE conversion. -/
def r0_transcript.block_rank.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  (c : r0_transcript.block_rank.closure) (i : Usize) :
  Result (Std.U32 × r0_transcript.block_rank.closure) := do
  let j ← 4#usize * i
  let b0 ← Array.index_usize c j
  let j1 ← j + 1#usize
  let b1 ← Array.index_usize c j1
  let j2 ← j + 2#usize
  let b2 ← Array.index_usize c j2
  let j3 ← j + 3#usize
  let b3 ← Array.index_usize c j3
  let w ← lift (core.num.U32.from_le_bytes (Array.make 4#usize [b0,b1,b2,b3]))
  ok (w,c)

def r0_transcript.block_rank.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
  (c : r0_transcript.block_rank.closure) (i : Usize) : Result Std.U32 := do
  let (w, _) ← r0_transcript.block_rank.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut c i
  ok w

@[reducible]
def r0_transcript.block_rank.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32 :
  core.ops.function.FnOnce r0_transcript.block_rank.closure Usize Std.U32 :=
  { call_once := r0_transcript.block_rank.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once }

@[reducible]
def r0_transcript.block_rank.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 :
  core.ops.function.FnMut r0_transcript.block_rank.closure Usize Std.U32 :=
  { FnOnceInst := r0_transcript.block_rank.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32
    call_mut := r0_transcript.block_rank.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut }

def r0_transcript.block_rank (block : Array Std.U8 32#usize) : Result (Array Std.U32 8#usize) :=
  core.array.from_fn 8#usize r0_transcript.block_rank.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 block

/-- Exact extracted `query_words` masking callback body. -/
def r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
  (c : r0_transcript.query_words.closure) (w : Std.U32) :
  Result (Std.U32 × r0_transcript.query_words.closure) := do
  let bound ← r0_transcript.QUERY_BOUND
  let maxWord ← bound - 1#u32
  let masked ← lift (w &&& maxWord)
  ok (masked,c)

def r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
  (c : r0_transcript.query_words.closure) (w : Std.U32) : Result Std.U32 := do
  let (masked, _) ← r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut c w
  ok masked

@[reducible]
def r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32 :
  core.ops.function.FnOnce r0_transcript.query_words.closure Std.U32 Std.U32 :=
  { call_once := r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once }

@[reducible]
def r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32 :
  core.ops.function.FnMut r0_transcript.query_words.closure Std.U32 Std.U32 :=
  { FnOnceInst := r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32
    call_mut := r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut }

def r0_transcript.query_words (block : Array Std.U8 32#usize) : Result (Array Std.U32 8#usize) := do
  let ranks ← r0_transcript.block_rank block
  core.array.Array.map r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32 ranks ()

end AspisR1QueryScanUnrolled


namespace AspisR1QueryScanUnrolled.r0_transcript

private theorem array_index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private def wordBytes (block : Array Std.U8 32#usize) (j : Nat) (hj : j < 8) :
    Array Std.U8 4#usize := ⟨[
      block.val[4*j]'(by
        have h32 : (32#usize : Usize).val = 32 := by scalar_tac
        rw [block.property, h32]
        omega),
      block.val[4*j+1]'(by
        have h32 : (32#usize : Usize).val = 32 := by scalar_tac
        rw [block.property, h32]
        omega),
      block.val[4*j+2]'(by
        have h32 : (32#usize : Usize).val = 32 := by scalar_tac
        rw [block.property, h32]
        omega),
      block.val[4*j+3]'(by
        have h32 : (32#usize : Usize).val = 32 := by scalar_tac
        rw [block.property, h32]
        omega)
    ], by simp⟩

private def wordAt (block : Array Std.U8 32#usize) (j : Nat) (hj : j < 8) : Std.U32 :=
  core.num.U32.from_le_bytes (wordBytes block j hj)

theorem block_rank_callback_call_mut_success
    (block : Array Std.U8 32#usize) (j : Usize) (hj : j.val < 8) :
    r0_transcript.block_rank.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      block j = .ok (wordAt block j.val hj, block) := by
  have hjmax : j.val ≤ Usize.max := by
    have hbound : j.val < 2 ^ System.Platform.numBits := by
      simpa only [Usize.numBits, UScalarTy.Usize_numBits_eq] using j.hBounds
    have hmax : Usize.max + 1 = 2 ^ System.Platform.numBits := Usize.max_succ_eq_pow
    omega
  have hmulBound : 4 * j.val ≤ Usize.max := by
    have h28 : 28 ≤ Usize.max := by scalar_tac
    omega
  have hmulSpec : (4#usize * j : Result Usize) ⦃z => z.val = 4 * j.val⦄ := by
    apply UScalar.mul_spec
    simpa only [UScalar.max_USize_eq, UScalar.ofNatCore_val_eq] using hmulBound
  obtain ⟨j0, hmul, hj0⟩ := WP.spec_imp_exists hmulSpec
  have hadd1Bound : j0.val + 1 ≤ Usize.max := by
    rw [hj0]
    have h31 : 31 ≤ Usize.max := by scalar_tac
    omega
  have hadd1Spec : (j0 + 1#usize : Result Usize) ⦃z => z.val = j0.val + 1⦄ := by
    apply UScalar.add_spec
    have hone : (1#usize).val = 1 := by scalar_tac
    simpa only [hone, UScalar.max_USize_eq] using hadd1Bound
  obtain ⟨j1, hadd1, hj1⟩ := WP.spec_imp_exists hadd1Spec
  have hadd2Bound : j0.val + 2 ≤ Usize.max := by
    rw [hj0]
    have h31 : 31 ≤ Usize.max := by scalar_tac
    omega
  have hadd2Spec : (j0 + 2#usize : Result Usize) ⦃z => z.val = j0.val + 2⦄ := by
    apply UScalar.add_spec
    have htwo : (2#usize).val = 2 := by scalar_tac
    simpa only [htwo, UScalar.max_USize_eq] using hadd2Bound
  obtain ⟨j2, hadd2, hj2⟩ := WP.spec_imp_exists hadd2Spec
  have hadd3Bound : j0.val + 3 ≤ Usize.max := by
    rw [hj0]
    have h31 : 31 ≤ Usize.max := by scalar_tac
    omega
  have hadd3Spec : (j0 + 3#usize : Result Usize) ⦃z => z.val = j0.val + 3⦄ := by
    apply UScalar.add_spec
    have hthree : (3#usize).val = 3 := by scalar_tac
    simpa only [hthree, UScalar.max_USize_eq] using hadd3Bound
  obtain ⟨j3, hadd3, hj3⟩ := WP.spec_imp_exists hadd3Spec
  have h32 : (32#usize : Usize).val = 32 := by scalar_tac
  have hread0 := array_index_usize_ok block j0 (by rw [hj0, h32]; omega)
  have hread1 := array_index_usize_ok block j1 (by rw [hj1, hj0, h32]; omega)
  have hread2 := array_index_usize_ok block j2 (by rw [hj2, hj0, h32]; omega)
  have hread3 := array_index_usize_ok block j3 (by rw [hj3, hj0, h32]; omega)
  unfold r0_transcript.block_rank.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  simp only [hmul, hread0, hadd1, hread1, hadd2, hread2, hadd3, hread3, bind_tc_ok]
  have hidx0 : j0.val = 4*j.val := hj0
  have hidx1 : j1.val = 4*j.val+1 := by rw [hj1, hj0]
  have hidx2 : j2.val = 4*j.val+2 := by rw [hj2, hj0]
  have hidx3 : j3.val = 4*j.val+3 := by rw [hj3, hj0]
  simp only [hidx0, hidx1, hidx2, hidx3]
  have hlen : block.val.length = 32 := by rw [block.property, h32]
  have hb0 : 4*j.val < block.val.length := by rw [hlen]; omega
  have hb1 : 4*j.val+1 < block.val.length := by rw [hlen]; omega
  have hb2 : 4*j.val+2 < block.val.length := by rw [hlen]; omega
  have hb3 : 4*j.val+3 < block.val.length := by rw [hlen]; omega
  have hbytes : Array.make 4#usize
      [block.val[4*j.val]'hb0, block.val[4*j.val+1]'hb1,
        block.val[4*j.val+2]'hb2, block.val[4*j.val+3]'hb3] =
      wordBytes block j.val hj := by
    apply Subtype.ext
    rfl
  rw [hbytes]
  rfl

#print axioms block_rank_callback_call_mut_success
end AspisR1QueryScanUnrolled.r0_transcript
namespace AspisR1SelectedMaskProbe

theorem arrayFromFnLoop_values_of_stable
    {T F : Type} {N : Usize}
    (callback : core.ops.function.FnMut F Usize T) (value : Nat → T)
    (fuel : Nat) (i : Usize) (f : F) (acc : List T)
    (out : List T) (fout : F)
    (hi : i.val ≤ N.val) (hbudget : N.val - i.val ≤ fuel)
    (hacc : acc.reverse = (List.range i.val).map value)
    (hstable : ∀ j : Usize, j.val < N.val →
      callback.call_mut f j = .ok (value j.val, f))
    (hrun : arrayFromFnLoop N callback fuel i f acc = .ok (out, fout)) :
    out = (List.range N.val).map value ∧ fout = f := by
  induction fuel generalizing i f acc out fout with
  | zero =>
      have hnot : ¬ i < N := by
        intro hlt
        have hltv : i.val < N.val := by simpa only [UScalar.lt_equiv] using hlt
        omega
      simp only [arrayFromFnLoop, hnot] at hrun
      cases Result.ok.inj hrun
      have hiN : i.val = N.val := by omega
      constructor <;> (first | simpa [hiN] using hacc | rfl)
  | succ fuel ih =>
      by_cases hlt : i < N
      · have hltv : i.val < N.val := by simpa only [UScalar.lt_equiv] using hlt
        have hcall := hstable i hltv
        have hNbound : N.val ≤ Usize.max := by
          have hNsize : N.val < 2 ^ Usize.numBits := by
            simpa [Usize.numBits, UScalarTy.Usize_numBits_eq] using N.hBounds
          have hmax : Usize.max + 1 = 2 ^ Usize.numBits := by
            rw [Usize.numBits]
            exact Usize.max_succ_eq_pow
          omega
        have haddBound : i.val + 1 ≤ Usize.max := by omega
        have haddSpec : (i + 1#usize : Result Usize) ⦃z => z.val = i.val + 1⦄ := by
          apply UScalar.add_spec
          have hone : (1#usize).val = 1 := by scalar_tac
          simpa only [hone, UScalar.max_USize_eq] using haddBound
        obtain ⟨i', hadd, hi'⟩ := Aeneas.Std.WP.spec_imp_exists haddSpec
        simp only [arrayFromFnLoop, hlt] at hrun
        rw [hcall, bind_tc_ok] at hrun
        simp only [hadd, bind_tc_ok] at hrun
        have hi'val : i'.val = i.val + 1 := hi'
        have hi'le : i'.val ≤ N.val := by rw [hi'val]; omega
        have hbudget' : N.val - i'.val ≤ fuel := by rw [hi'val]; omega
        have hacc' : (value i.val :: acc).reverse = (List.range i'.val).map value := by
          rw [List.reverse_cons, hacc, hi'val, List.range_succ]
          simp
        exact ih i' f (value i.val :: acc) out fout hi'le hbudget' hacc' hstable hrun
      · have hiN : i.val = N.val := by
          have hnotval : ¬ i.val < N.val := by
            intro h
            apply hlt
            simpa only [UScalar.lt_equiv] using h
          omega
        simp only [arrayFromFnLoop, hlt] at hrun
        cases Result.ok.inj hrun
        constructor <;> (first | simpa [hiN] using hacc | rfl)

end AspisR1SelectedMaskProbe
namespace AspisR1QueryScanUnrolled.r0_transcript

def blockRankWord (block : Array Std.U8 32#usize) (j : Nat) : Std.U32 :=
  if hj : j < 8 then wordAt block j hj else 0#u32

theorem block_rank_success_words_in_order
    (block : Array Std.U8 32#usize) (out : Array Std.U32 8#usize)
    (hrank : r0_transcript.block_rank block = .ok out) :
    out.val = (List.range 8).map (blockRankWord block) := by
  let callback := r0_transcript.block_rank.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
  have h8 : (8#usize : Usize).val = 8 := by scalar_tac
  have h0 : (0#usize : Usize).val = 0 := by scalar_tac
  have hstable : ∀ j : Usize, j.val < (8#usize : Usize).val →
      callback.call_mut block j = .ok (blockRankWord block j.val, block) := by
    intro j hj
    have hj8 : j.val < 8 := by simpa [h8] using hj
    have h := block_rank_callback_call_mut_success block j hj8
    simpa [callback, blockRankWord, hj8] using h
  unfold r0_transcript.block_rank at hrank
  simp only [AspisR1QueryScanUnrolled.core.array.from_fn] at hrank
  unfold AspisR1SelectedMaskProbe.core.array.from_fn at hrank
  split at hrank
  · rename_i values fout hloop
    have hout : (⟨values, by
        exact AspisR1SelectedMaskProbe.arrayFromFnLoop_length_of_success
          (8#usize) callback ((8#usize : Usize).val + 1) 0#usize block []
          values fout (by rw [h0]; omega) (by simp) (by omega) hloop⟩ :
        Array Std.U32 8#usize) = out := Result.ok.inj hrank
    have hvalues := AspisR1SelectedMaskProbe.arrayFromFnLoop_values_of_stable
      callback (blockRankWord block) ((8#usize : Usize).val + 1)
      0#usize block [] values fout (by rw [h0,h8]; omega) (by rw [h0,h8]; omega)
      (by simp [h0]) hstable hloop
    have hv : values = (List.range 8).map (blockRankWord block) := by
      simpa [h8] using hvalues.1
    exact (congrArg (fun a : Array Std.U32 8#usize => a.val) hout).symm.trans hv
  · simp at hrank
  ·
    have hdiv : div? (Result.div : Result (Array Std.U32 8#usize)) = true := rfl
    rw [hrank] at hdiv
    simp [div?] at hdiv


theorem block_rank_word_from_le_bytes
    (block : Array Std.U8 32#usize) (j : Nat) (hj : j < 8) :
    (wordAt block j hj).val =
      (BitVec.fromLEBytes ((wordBytes block j hj).val.map Std.U8.bv)).toNat := by
  rfl

#print axioms block_rank_word_from_le_bytes

#print axioms block_rank_success_words_in_order
end AspisR1QueryScanUnrolled.r0_transcript

namespace AspisR1QueryScanUnrolled.r0_transcript

def queryMaskWord (w : Std.U32) : Std.U32 := w &&& 262143#u32

theorem query_mask_call_mut_exact (c : query_words.closure) (w : Std.U32) :
    query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut c w =
      .ok (queryMaskWord w, c) := by
  have hbound : r0_transcript.QUERY_BOUND = .ok 262144#u32 := by
    unfold r0_transcript.QUERY_BOUND
    rfl
  have hsub : 262144#u32 - 1#u32 = ok 262143#u32 := rfl
  simp [query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut,
    hbound, hsub, queryMaskWord, lift]

private theorem mapState_stable {T U F : Type}
    (call : F → T → Result (U × F)) (f : F) (g : T → U) (xs : List T)
    (hstable : ∀ x, x ∈ xs → call f x = .ok (g x, f)) :
    AspisV8R19.TraversalRuntime.mapState call xs f = .ok (xs.map g, f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := hstable x (by simp)
      have htail : ∀ y, y ∈ xs → call f y = .ok (g y, f) := by
        intro y hy
        exact hstable y (List.mem_cons_of_mem x hy)
      simp only [AspisV8R19.TraversalRuntime.mapState, hx, bind_tc_ok,
        List.map_cons, ih htail]

/-- Exact byte parser/mask output for every successful query_words result.
The only standard-library construction boundary is the from_fn model used by block_rank. -/
theorem query_words_success_byte_mask
    (block : Array Std.U8 32#usize) (words : Array Std.U32 8#usize)
    (hqw : r0_transcript.query_words block = .ok words) :
    words.val = (List.range 8).map
      (fun j => queryMaskWord (blockRankWord block j)) := by
  unfold r0_transcript.query_words at hqw
  cases hrank : r0_transcript.block_rank block with
  | fail e => simp [hrank] at hqw
  | div => simp [hrank] at hqw
  | ok ranks =>
      cases hmap : core.array.Array.map
          r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32 ranks () with
      | fail e => simp [hrank,hmap] at hqw
      | div => simp [hrank,hmap] at hqw
      | ok out =>
          have hout : out = words := by simpa [hrank,hmap] using hqw
          have horder := block_rank_success_words_in_order block ranks hrank
          let callback := r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32
          have hstable : ∀ x, x ∈ ranks.val →
              callback.call_mut () x = .ok (queryMaskWord x, ()) := by
            intro x _
            exact query_mask_call_mut_exact () x
          have hstate := mapState_stable callback.call_mut () queryMaskWord ranks.val hstable
          let masked : Array Std.U32 8#usize :=
            ⟨ranks.val.map queryMaskWord, by simpa using ranks.property⟩
          have hmodel : core.array.Array.map callback ranks () = .ok masked := by
            change Aeneas.Std.core.array.Array.map callback ranks () = .ok masked
            have h := Aeneas.Std.core.array.Array.map_success callback ranks ()
              (ranks.val.map queryMaskWord) () hstate
            simpa [masked] using h
          have hvals : out.val = ranks.val.map queryMaskWord := by
            have heq : out = masked := Result.ok.inj (hmap.symm.trans hmodel)
            exact congrArg (fun a : Array Std.U32 8#usize => a.val) heq
          subst words
          rw [hvals, horder]
          rfl

#print axioms query_words_success_byte_mask
end AspisR1QueryScanUnrolled.r0_transcript

