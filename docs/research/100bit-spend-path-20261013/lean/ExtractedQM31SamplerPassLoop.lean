import ExtractedQM31SamplerPass

/-! Complete owned quotient-array correspondence for the extracted loop. -/
set_option autoImplicit false

namespace AspisR1.ExtractedQM31SamplerPassLoop
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1Qm31SamplerIndex
open SamplerMachineBounds SamplerWord SamplerWordPass ExtractedQM31SamplerPass

def decode32 (x : U32) : UInt32 := UInt32.ofNat x.val
def decode64 (x : U64) : UInt64 := UInt64.ofNat x.val
def words (rank : Array U32 8#usize) : List UInt32 := rank.val.map decode32

theorem decode32_val (x : U32) : (decode32 x).toNat = x.val := by
  exact UInt32.toNat_ofNat_of_lt' x.bv.isLt

theorem decode64_val (x : U64) : (decode64 x).toNat = x.val := by
  exact UInt64.toNat_ofNat_of_lt' x.bv.isLt

theorem words_length (rank : Array U32 8#usize) : (words rank).length = 8 := by
  simp only [words, List.length_map]
  exact rank.property

theorem words_set (rank : Array U32 8#usize) (j : Usize) (q : U32) :
    words (rank.set j q) = (words rank).set j.val (decode32 q) := by
  simp only [words, Array.set_val_eq, List.map_set]

theorem loop_unroll (rank : Array U32 8#usize) (r : U64) (j : Usize) :
    sampler.qm31_div_pass_loop rank r j = (do
      let flow ← sampler.qm31_div_pass_loop.body rank r j
      match flow with
      | cont (rank1, r1, j1) => sampler.qm31_div_pass_loop rank1 r1 j1
      | done out => ok out) := by
  conv_lhs => unfold sampler.qm31_div_pass_loop; rw [loop]
  cases hb : sampler.qm31_div_pass_loop.body rank r j with
  | fail e => simp only [hb, bind_tc_fail]
  | div => simp only [hb, bind_tc_div]
  | ok flow =>
    cases flow with
    | done out => simp only [hb, bind_tc_ok]
    | cont next => simp only [hb, bind_tc_ok]; rfl

/-- Every remaining word is divided, with the complete quotient prefix and
untouched suffix identified. The source loop is proved to return successfully. -/
theorem loop_correct (rank : Array U32 8#usize) (r : U64) (j : Usize)
    (hr : r.val < P) (hj : j.val ≤ 8) :
    ∃ (out : Array U32 8#usize) (rem : U64),
      sampler.qm31_div_pass_loop rank r j = ok (out, rem) ∧
      rem.val = (machineProcess (decode64 r) ((words rank).take j.val).reverse).1.toNat ∧
      words out = (machineProcess (decode64 r) ((words rank).take j.val).reverse).2.reverse
        ++ (words rank).drop j.val ∧
      rem.val < P := by
  by_cases hz : j.val = 0
  · have hg : ¬ j > 0#usize := by change ¬ 0 < j.val; omega
    refine ⟨rank, r, ?_, ?_, ?_, hr⟩
    · rw [loop_unroll]
      simp only [sampler.qm31_div_pass_loop.body, hg, if_false, bind_tc_ok]
    · simp only [hz, List.take_zero, List.reverse_nil, machineProcess, decode64_val]
    · simp only [hz, List.take_zero, List.reverse_nil, machineProcess,
        List.drop_zero, List.nil_append]
  · have hj0 : 0 < j.val := Nat.pos_of_ne_zero hz
    obtain ⟨j1, q, r1, hbody, hvj, hvq, hvr, hr1⟩ := body_success rank r j hr hj0 hj
    let n := j.val - 1
    have hn : j.val = n + 1 := by omega
    have hj1 : j1.val = n := hvj
    have hlength : rank.val.length = 8 := rank.property
    have hnrank : n < rank.val.length := by omega
    have hnwords : n < (words rank).length := by rw [words_length]; omega
    let d : U32 := rank.val[n]
    have hqmodel : decode32 q = (machineStep (decode64 r) (decode32 d)).1 := by
      apply UInt32.toNat.inj
      rw [decode32_val, machineStep_quotient_toNat _ (by rw [decode64_val]; exact hr)]
      simpa only [decode64_val, decode32_val, B, d, n] using hvq
    have hrmodel : decode64 r1 =
        UInt64.ofNat (machineStep (decode64 r) (decode32 d)).2.toNat := by
      apply UInt64.toNat.inj
      rw [decode64_val, uint32_to_uint64_toNat,
        machineStep_remainder_toNat _ (by rw [decode64_val]; exact hr)]
      simpa only [decode64_val, decode32_val, B, d, n] using hvr
    have hget : (words rank)[n] = decode32 d := by
      simp only [words, List.getElem_map, d]
    have hinput : ((words rank).take j.val).reverse =
        decode32 d :: ((words rank).take n).reverse := by
      rw [hn, List.take_succ_eq_append_getElem hnwords, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append, hget]
    have htake : ((words (rank.set j1 q)).take j1.val).reverse =
        ((words rank).take n).reverse := by
      rw [words_set, hj1, List.take_set_of_le (Nat.le_refl n)]
    have hdrop : (words (rank.set j1 q)).drop j1.val =
        decode32 q :: (words rank).drop j.val := by
      rw [words_set, hj1, List.drop_set]
      simp only [Nat.lt_irrefl, if_false, Nat.sub_self]
      rw [List.drop_eq_getElem_cons hnwords, hn]
      rfl
    have hmodel : machineProcess (decode64 r) ((words rank).take j.val).reverse =
        let tail := machineProcess (decode64 r1) ((words rank).take n).reverse
        (tail.1, decode32 q :: tail.2) := by
      rw [hinput]
      simp only [machineProcess]
      rw [← hrmodel, ← hqmodel]
    obtain ⟨out, rem, hexec, hrem, hout, hrembound⟩ :=
      loop_correct (rank.set j1 q) r1 j1 hr1 (by omega)
    refine ⟨out, rem, ?_, ?_, ?_, hrembound⟩
    · rw [loop_unroll, hbody]
      simpa only [bind_tc_ok] using hexec
    · rw [hmodel]
      simpa only [htake] using hrem
    · rw [hmodel]
      simpa only [htake, hdrop, List.reverse_cons, List.append_assoc,
        List.singleton_append] using hout
termination_by j.val
decreasing_by omega

#print axioms decode32_val
#print axioms decode64_val
#print axioms words_set
#print axioms loop_unroll
#print axioms loop_correct

end AspisR1.ExtractedQM31SamplerPassLoop
