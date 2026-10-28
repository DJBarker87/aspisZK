import R1Z.PV_B2_C_SamplerEnvironment
import AspisR1Post25SamplerIndexedAddSmallCandidate.Funs
import Aeneas
import R1SourceSamplerByteRank
import GammaCandidateLowQuotient
import IndexedCandidateAddSmallWrapperNatModelV3
-- Unchanged previously checked component PV_B2_C_AddSmallAgreement
section
set_option autoImplicit false
namespace PV_B2_C_AddSmallAgreement
open Aeneas Aeneas.Std Result ControlFlow
namespace N
abbrev body := PV_B2_C_Sampler.host_sampler.add_small_base_p_loop.body
abbrev run := PV_B2_C_Sampler.host_sampler.add_small_base_p_loop
end N
namespace O
abbrev body := AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p_loop.body
abbrev run := AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p_loop
end O

/-- Complete Result equality on arbitrary typed digits, carry and counter. -/
theorem body (ds : Array U32 8#usize) (n : U32) (i : Usize) :
    N.body ds n i = O.body ds n i := by
  unfold N.body O.body
    PV_B2_C_Sampler.host_sampler.add_small_base_p_loop.body
    AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p_loop.body
  by_cases h : i < 8#usize
  · have hi : i.val < 8 := h
    simp only [if_pos h,lift,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro d _
    have hs := PV_B2_C_MachineArithmetic.u64_add_exact
      (core.convert.num.FromU64U32.from d)
      (core.convert.num.FromU64U32.from n) (by scalar_tac)
    simp only [hs,PV_B2_C_MachineArithmetic.add_exact i 1#usize (by scalar_tac),
      PV_B2_C_Sampler.aspis_core.field.P,
      AspisR1Post25SamplerIndexedAddSmallCandidate.field.P,bind_tc_ok]
  · simp only [if_neg h]

theorem loop (ds : Array U32 8#usize) (n : U32) (i : Usize) :
    N.run ds n i = O.run ds n i := by
  unfold N.run O.run
    PV_B2_C_Sampler.host_sampler.add_small_base_p_loop
    AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p_loop
  have hb : (fun (a,b,c) => N.body a b c) = (fun (a,b,c) => O.body a b c) := by
    funext ⟨a,b,c⟩
    exact body a b c
  rw [hb]

theorem wrapper (ds : Array U32 8#usize) (n : U32) :
    PV_B2_C_Sampler.host_sampler.add_small_base_p ds n =
      AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p ds n := by
  unfold PV_B2_C_Sampler.host_sampler.add_small_base_p
    AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p
  have h := loop ds n 0#usize
  change (N.run ds n 0#usize >>= _) = (O.run ds n 0#usize >>= _)
  rw [h]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨out,carry⟩ _
  rfl

#print axioms body
#print axioms loop
#print axioms wrapper
end PV_B2_C_AddSmallAgreement

end
-- Unchanged previously checked component PV_B2_C_GammaNumeric
section
set_option autoImplicit false
namespace PV_B2_C_GammaNumeric
open Aeneas Aeneas.Std Result
variable {α : Type}
structure GammaHelpers (α : Type) where
  low : Array U8 32#usize → Result (Array U32 8#usize × U32)
  add : Array U32 8#usize → U32 → Result (Bool × Array U32 8#usize)
  decode : Array U32 8#usize → Result α

def sample (ops : GammaHelpers α) (block : Array U8 32#usize) : Result α := do
  let (digits,q) ← ops.low block
  let n ← q + 1#u32
  let (wrapped,ds1) ← ops.add digits n
  let ds2 ← if wrapped then do
    let (_,ds2) ← ops.add ds1 1#u32
    ok ds2
  else ok ds1
  ops.decode ds2
open AspisR1 AspisR1.SamplerNatModel AspisR1.SamplerMachineBounds
open AspisR1.SamplerAddDigits AspisR1.SamplerAddBridge
open AspisR1.SourceSamplerByteRank
abbrev Digits := Array U32 8#usize
abbrev Bytes32 := Array U8 32#usize

def values (ds : Digits) : List Nat := ds.val.map UScalar.val
def Canonical (ds : Digits) : Prop := ∀ d ∈ values ds, d < P

structure HelpersRefine (ops : GammaHelpers α) : Prop where
  low : ∀ block ds q, ops.low block = .ok (ds,q) →
    values ds = ordinaryDigits (rank block) ∧ q.val = rank block / P^8
  add : ∀ ds n wrapped out, Canonical ds → n.val ≤ 257 →
    ops.add ds n = .ok (wrapped,out) →
      values out = (addDigits P n.val (values ds)).1 ∧
      (wrapped = false ↔ (addDigits P n.val (values ds)).2 = 0)

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem pair_bind_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b) = .ok v) :
    ∃ a b, m = .ok (a,b) ∧ k a b = .ok v := by
  cases m with
  | ok pair => cases pair with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem increment_value (q n : U32) (hq : q.val ≤ 256)
    (h : (q + 1#u32 : Result U32) = .ok n) : n.val = q.val + 1 := by
  have hs : (q + 1#u32 : Result U32) ⦃z => z.val = q.val + 1⦄ := by
    apply UScalar.add_spec
    change q.val + 1 ≤ UScalar.max UScalarTy.U32
    have hc : 257 ≤ UScalar.max UScalarTy.U32 := by
      rw [UScalar.max_UScalarTy_U32_eq]
      norm_num [U32.max, U32.numBits]
    omega
  obtain ⟨n1,hn1,hv⟩ := WP.spec_imp_exists hs
  have he : n1 = n := Result.ok.inj (hn1.symm.trans h)
  subst n1
  exact hv

theorem gamma_digits_success (ops : GammaHelpers α) (R : HelpersRefine ops)
    (block : Bytes32) (out : α)
    (h : sample ops block = .ok out) :
    ∃ ds : Digits,
      ops.decode ds = .ok out ∧ values ds = gammaDigits (rank block) := by
  unfold sample at h
  obtain ⟨lowPair,hlow,h⟩ := bind_success (ops.low block) _ _ h
  rcases lowPair with ⟨digits,q⟩
  obtain ⟨n,hn,h⟩ := bind_success (q + 1#u32) _ _ h
  obtain ⟨addPair,hadd,h⟩ := bind_success (ops.add digits n) _ _ h
  rcases addPair with ⟨wrapped,digits1⟩
  obtain ⟨hd,hq⟩ := R.low block digits q hlow
  have hq256 : q.val ≤ 256 := by
    rw [hq]
    exact rank_div_P8_le_256 (rank_lt block)
  have hnval := increment_value q n hq256 hn
  have hn257 : n.val ≤ 257 := by omega
  have Cdigits : Canonical digits := by
    unfold Canonical
    rw [hd]
    exact lowDigits_canonical P_pos 8 (rank block)
  obtain ⟨hfirst,hcarry⟩ := R.add digits n wrapped digits1 Cdigits hn257 hadd
  have Cdigits1 : Canonical digits1 := by
    unfold Canonical
    rw [hfirst]
    exact addDigits_output_digits_lt P _ _ P_pos
  rw [hnval,hd,hq] at hfirst hcarry
  cases wrapped with
  | false =>
      change ops.decode digits1 = .ok out at h
      refine ⟨digits1,h,?_⟩
      have hz := hcarry.mp rfl
      unfold gammaDigits endAround
      rw [if_pos hz]
      exact hfirst
  | true =>
      change ((do
        let pair ← ops.add digits1 1#u32
        ok pair.2) >>= ops.decode) = .ok out at h
      with_unfolding_all simp only [bind_assoc_eq,bind_tc_ok] at h
      have hflat : (do let pair ← ops.add digits1 1#u32; ops.decode pair.2) = .ok out := h
      obtain ⟨pair,hsecond,h⟩ := bind_success (ops.add digits1 1#u32) _ _ hflat
      rcases pair with ⟨wrappedAgain,digits2⟩
      change ops.decode digits2 = .ok out at h
      obtain ⟨hsecondValue,_⟩ := R.add digits1 1#u32 wrappedAgain digits2 Cdigits1 (by decide) hsecond
      have hz : (addDigits P (rank block / P^8 + 1) (ordinaryDigits (rank block))).2 ≠ 0 := by
        intro hz
        have hfalse := hcarry.mpr hz
        cases hfalse
      refine ⟨digits2,h,?_⟩
      unfold gammaDigits endAround
      rw [if_neg hz]
      simpa only [show (1#u32).val = 1 by rfl,hfirst] using hsecondValue

open AspisR1 AspisR1.SamplerNatModel AspisR1.SamplerMachineBounds
open AspisR1.SamplerAddDigits AspisR1.SourceSamplerByteRank

theorem gamma_rank_success (ops : GammaHelpers α) (R : HelpersRefine ops)
    (block : Bytes32) (out : α)
    (h : sample ops block = .ok out) :
    ∃ ds : Digits,
      ops.decode ds = .ok out ∧ Canonical ds ∧
      digitsValue P (values ds) = rank block % (P^8 - 1) + 1 ∧
      0 < digitsValue P (values ds) ∧ digitsValue P (values ds) < P^8 := by
  obtain ⟨ds,hdecode,hdigits⟩ := gamma_digits_success ops R block out h
  have hcanonical : Canonical ds := by
    unfold Canonical
    rw [hdigits]
    exact (gammaDigits_canonical (rank block)).2
  refine ⟨ds,hdecode,hcanonical,?_,?_⟩
  · rw [hdigits]
    exact gammaDigits_value (rank_lt block)
  · rw [hdigits]
    exact gammaDigits_value_bounds (rank_lt block)
#print axioms bind_success
#print axioms pair_bind_success
#print axioms increment_value
#print axioms gamma_digits_success
#print axioms gamma_rank_success
end PV_B2_C_GammaNumeric

end
-- Unchanged previously checked component PV_B2_C_GammaTotal
section
set_option autoImplicit false
namespace PV_B2_C_GammaNumeric
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1.SamplerNatModel AspisR1.SamplerMachineBounds
open AspisR1.SamplerAddDigits AspisR1.SourceSamplerByteRank
variable {α : Type}

/-- Explicit local totality obligations, discharged for the copied source below;
this structure is not a privacy trust item or an endpoint assumption. -/
structure HelpersTotal (ops : GammaHelpers α) : Prop where
  low : ∀ (block : Bytes32), ∃ (ds : Digits) (q : U32), ops.low block = ok (ds,q)
  add : ∀ (ds : Digits) (n : U32), Canonical ds → n.val ≤ 257 →
    ∃ wrapped out, ops.add ds n = ok (wrapped,out)
  decode : ∀ (ds : Digits), Canonical ds → ∃ out, ops.decode ds = ok out

theorem sample_total (ops : GammaHelpers α) (R : HelpersRefine ops)
    (H : HelpersTotal ops) (block : Bytes32) : ∃ out, sample ops block = ok out := by
  obtain ⟨ds,q,hlow⟩ := H.low block
  obtain ⟨hd,hq⟩ := R.low block ds q hlow
  have hq256 : q.val ≤ 256 := by
    rw [hq]
    exact rank_div_P8_le_256 (rank_lt block)
  have hc : Canonical ds := by
    unfold Canonical
    rw [hd]
    exact lowDigits_canonical P_pos 8 (rank block)
  obtain ⟨n,hn,hv⟩ := WP.spec_imp_exists (U32.add_spec (x := q) (y := 1#u32) (by scalar_tac))
  have hn257 : n.val ≤ 257 := by
    have hnval : n.val = q.val + 1 := by simpa using hv
    omega
  obtain ⟨wrapped,ds1,hadd⟩ := H.add ds n hc hn257
  obtain ⟨hfirst,_⟩ := R.add ds n wrapped ds1 hc hn257 hadd
  have hc1 : Canonical ds1 := by
    unfold Canonical
    rw [hfirst]
    exact addDigits_output_digits_lt P _ _ P_pos
  cases wrapped with
  | false =>
    obtain ⟨out,hdecode⟩ := H.decode ds1 hc1
    refine ⟨out,?_⟩
    unfold sample
    rw [hlow]
    change ((q + 1#u32 : Result U32) >>= _) = ok out
    rw [hn]
    change (ops.add ds n >>= _) = ok out
    rw [hadd]
    change ops.decode ds1 = ok out
    exact hdecode
  | true =>
    obtain ⟨wrapped2,ds2,hsecond⟩ := H.add ds1 1#u32 hc1 (by decide)
    obtain ⟨hsecondValue,_⟩ := R.add ds1 1#u32 wrapped2 ds2 hc1 (by decide) hsecond
    have hc2 : Canonical ds2 := by
      unfold Canonical
      rw [hsecondValue]
      exact addDigits_output_digits_lt P _ _ P_pos
    obtain ⟨out,hdecode⟩ := H.decode ds2 hc2
    refine ⟨out,?_⟩
    unfold sample
    rw [hlow]
    change ((q + 1#u32 : Result U32) >>= _) = ok out
    rw [hn]
    change (ops.add ds n >>= _) = ok out
    rw [hadd]
    change ((do let pair ← ops.add ds1 1#u32; ok pair.2) >>= ops.decode) = ok out
    rw [hsecond]
    change ops.decode ds2 = ok out
    exact hdecode

#print axioms sample_total
end PV_B2_C_GammaNumeric

end
-- Unchanged previously checked component PV_B2_C_GammaHelpers
section
set_option autoImplicit false
namespace PV_B2_C_GammaHelpers
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1.SamplerNatModel AspisR1.SamplerMachineBounds
open AspisR1.SamplerAddDigits AspisR1.SourceSamplerByteRank
open PV_B2_C_GammaNumeric
abbrev E := PV_B2_C_249.aspis_core.field.wide_exact.WideExact
abbrev N := PV_B2_C_Sampler.host_sampler.low_base_p_digits
abbrev O := AspisR1Post25Sampler.sampler.low_base_p_digits

def ops : GammaHelpers E where
  low := PV_B2_C_Sampler.host_sampler.low_base_p_digits
  add := PV_B2_C_Sampler.host_sampler.add_small_base_p
  decode := PV_B2_C_Sampler.host_sampler.decode8

theorem low_agreement (b : Bytes32) : N b = O b :=
  (PV_B2_C_LowDigits.source b).trans (R1Z.PV_B2_C_CheckedDigits.digits b)

theorem low_refines (b : Bytes32) (ds : Digits) (q : U32)
    (h : N b = ok (ds,q)) :
    values ds = ordinaryDigits (rank b) ∧ q.val = rank b / P^8 := by
  exact AspisR1GammaCaller.DigitsModel.low_candidate_refines b ds q
    ((low_agreement b).symm.trans h)

theorem canonical_indexed (ds : Digits) (h : Canonical ds) :
    AspisR1.ExtractedIndexedAddSmallNatModelV1.Canonical ds := by
  intro j hj
  have h8 : (8#usize).val = 8 := by decide
  have hlen : j < ds.val.length := by
    rw [ds.property,h8]
    exact hj
  have hm : (ds.val[j]'hlen).val ∈ values ds := by
    exact List.mem_map.mpr ⟨_,List.getElem_mem hlen,rfl⟩
  change (ds.val[j]'(by rw [ds.property,h8];exact hj)).val < P
  exact h _ hm

theorem add_total_value (ds : Digits) (n : U32) (hc : Canonical ds) (hn : n.val ≤ 257) :
    ∃ carry : U32, ∃ out : Digits,
      ops.add ds n = ok (carry != 0#u32,out) ∧
      values out = (addDigits P n.val (values ds)).1 ∧
      carry.val = (addDigits P n.val (values ds)).2 := by
  obtain ⟨carry,out,he,hv,hcarry⟩ :=
    AspisR1.ExtractedIndexedAddSmallWrapperNatModelV1.add_small_base_p_refines_addDigits
      ds n (canonical_indexed ds hc) hn
  refine ⟨carry,out,?_,hv,hcarry⟩
  exact (PV_B2_C_AddSmallAgreement.wrapper ds n).trans he

theorem add_refines (ds : Digits) (n : U32) (wrapped : Bool) (out : Digits)
    (hc : Canonical ds) (hn : n.val ≤ 257) (he : ops.add ds n = ok (wrapped,out)) :
    values out = (addDigits P n.val (values ds)).1 ∧
      (wrapped = false ↔ (addDigits P n.val (values ds)).2 = 0) := by
  obtain ⟨carry,out1,he1,hv,hcarry⟩ := add_total_value ds n hc hn
  have hp := Result.ok.inj (he1.symm.trans he)
  have hw : (carry != 0#u32) = wrapped := congrArg Prod.fst hp
  have ho : out1 = out := congrArg Prod.snd hp
  subst out1
  refine ⟨hv,?_⟩
  rw [← hw]
  constructor
  · intro hf
    have hzero : carry = 0#u32 := by
      by_contra hne
      have ht : (carry != 0#u32) = true := by simpa using hne
      rw [ht] at hf
      cases hf
    have hval := congrArg UScalar.val hzero
    rw [hcarry] at hval
    exact hval
  · intro hz
    have hval : carry.val = 0 := hcarry.trans hz
    have heq : carry = 0#u32 := UScalar.eq_of_val_eq hval
    rw [heq]
    decide

theorem decode_total (ds : Digits) (hc : Canonical ds) :
    ∃ out : E, ops.decode ds = ok out := by
  refine ⟨PV_B2_C_ArrayDigits.raw ds,PV_B2_C_ArrayDigits.decode ds ?_⟩
  intro i
  have hm : (PV_B2_C_ArrayDigits.limb ds i).val ∈ values ds := by
    exact List.mem_map.mpr ⟨_,List.getElem_mem (by rw [ds.property];exact i.isLt),rfl⟩
  exact hc _ hm

theorem refine_source : HelpersRefine ops where
  low := low_refines
  add := add_refines

theorem total_source : HelpersTotal ops where
  low := by
    intro b
    obtain ⟨ds,q,he,_,_⟩ := PV_B2_C_RankDigits.source b
    exact ⟨ds,q,he⟩
  add := by
    intro ds n hc hn
    obtain ⟨carry,out,he,_,_⟩ := add_total_value ds n hc hn
    exact ⟨_,_,he⟩
  decode := decode_total

#print axioms low_agreement
#print axioms low_refines
#print axioms canonical_indexed
#print axioms add_total_value
#print axioms add_refines
#print axioms decode_total
#print axioms refine_source
#print axioms total_source
end PV_B2_C_GammaHelpers

end
-- Unchanged previously checked component PV_B2_C_U32Arithmetic
section
set_option autoImplicit false
namespace PV_B2_C_U32Arithmetic
open Aeneas Aeneas.Std Result WP
 theorem add_exact (x y : U32) (h : x.val + y.val ≤ U32.max) :
    x + y = ok (U32.wrapping_add x y) := by
  obtain ⟨z,hz,hv⟩ := spec_imp_exists (U32.add_spec (x := x) (y := y) h)
  have he : z = U32.wrapping_add x y := by
    apply UScalar.eq_of_val_eq
    rw [U32.wrapping_add_val_eq, Nat.mod_eq_of_lt (by
      simpa only [UScalar.size, UScalarTy.numBits, U32.numBits] using
        (show x.val + y.val < 2^U32.numBits from by
          have hp : 0 < 2^U32.numBits := by positivity
          rw [U32.max] at h
          omega))]
    exact hv
  simpa only [he] using hz


#print axioms add_exact
end PV_B2_C_U32Arithmetic

end
-- Unchanged previously checked component PV_B2_C_GammaSource
section
set_option autoImplicit false
namespace PV_B2_C_GammaSource
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1.SamplerNatModel AspisR1.SamplerMachineBounds
open AspisR1.SamplerAddDigits AspisR1.SourceSamplerByteRank
open PV_B2_C_GammaNumeric PV_B2_C_GammaHelpers

/-- Checked and wrapping increments agree because the proved high quotient
is at most 256; no input rank is evaluated concretely. -/
theorem normalized_eq (b : Bytes32) :
    PV_B2_C_Sampler.host_sampler.gamma_sample b = sample ops b := by
  obtain ⟨ds,q,hlow,_,_⟩ := PV_B2_C_RankDigits.source b
  have hq := (low_refines b ds q hlow).2
  have hq256 : q.val ≤ 256 := by
    rw [hq]
    exact rank_div_P8_le_256 (rank_lt b)
  have hi := PV_B2_C_U32Arithmetic.add_exact q 1#u32 (by scalar_tac)
  let tail : Digits → U32 → Result E := fun digits n => do
    let (wrapped,ds1) ← PV_B2_C_Sampler.host_sampler.add_small_base_p digits n
    let ds2 ← if wrapped then do
      let (_,ds2) ← PV_B2_C_Sampler.host_sampler.add_small_base_p ds1 1#u32
      ok ds2
    else ok ds1
    PV_B2_C_Sampler.host_sampler.decode8 ds2
  have hl : PV_B2_C_Sampler.host_sampler.gamma_sample b = tail ds (U32.wrapping_add q 1#u32) := by
    unfold PV_B2_C_Sampler.host_sampler.gamma_sample
    rw [hlow]
    rfl
  have hr : sample ops b = (do let n ← q+1#u32; tail ds n) := by
    unfold sample
    change (PV_B2_C_Sampler.host_sampler.low_base_p_digits b >>= _) = _
    rw [hlow]
    rfl
  rw [hl,hr,hi,bind_tc_ok]

theorem canonical_array (ds : Digits) (hc : Canonical ds) : PV_B2_C_ArrayDigits.canonical ds := by
  intro i
  have hm : (PV_B2_C_ArrayDigits.limb ds i).val ∈ values ds := by
    exact List.mem_map.mpr ⟨_,List.getElem_mem (by rw [ds.property];exact i.isLt),rfl⟩
  exact hc _ hm

/-- Complete Result success and exact nonzero rank formula for every block,
on the exact raw extracted scalar structures. No success hypothesis. -/
theorem normalized_source (b : Bytes32) :
    ∃ ds : Digits,
      PV_B2_C_Sampler.host_sampler.gamma_sample b = ok (PV_B2_C_ArrayDigits.raw ds) ∧
      Canonical ds ∧ digitsValue P (values ds) = rank b % (P^8-1)+1 ∧
      0 < digitsValue P (values ds) ∧ digitsValue P (values ds) < P^8 := by
  obtain ⟨out,he⟩ := sample_total ops refine_source total_source b
  obtain ⟨ds,hdecode,hcanon,hrank,hpos,hbound⟩ :=
    gamma_rank_success ops refine_source b out he
  have hd := PV_B2_C_ArrayDigits.decode ds (canonical_array ds hcanon)
  have ho : out = PV_B2_C_ArrayDigits.raw ds := Result.ok.inj (hdecode.symm.trans hd)
  subst out
  exact ⟨ds,(normalized_eq b).trans he,hcanon,hrank,hpos,hbound⟩

/-- The presentation's field reconstruction is identity on this raw carrier. -/
theorem carrier_identity (v : E) : PV_B2_C_SamplerCarrier.toNative v = v := by
  cases v
  rfl

theorem result_identity (r : Result E) :
    PV_B2_C_SamplerCarrier.mapResult PV_B2_C_SamplerCarrier.toNative r = r := by
  cases r <;> simp only [PV_B2_C_SamplerCarrier.mapResult,carrier_identity]

theorem raw_eq (b : Bytes32) :
    PV_B2_C_249.host_sampler.gamma_sample b = PV_B2_C_Sampler.host_sampler.gamma_sample b := by
  have h := PV_B2_C_GammaCarrier.source b
  rw [result_identity] at h
  exact h

/-- Unmodified raw emission: complete Result and gamma rank, all byte inputs.
This is a copy-source law, not original/copy/native or V256 installation. -/
theorem op249_source (b : Bytes32) :
    ∃ ds : Digits,
      PV_B2_C_249.host_sampler.gamma_sample b = ok (PV_B2_C_ArrayDigits.raw ds) ∧
      Canonical ds ∧ digitsValue P (values ds) = rank b % (P^8-1)+1 ∧
      0 < digitsValue P (values ds) ∧ digitsValue P (values ds) < P^8 := by
  rw [raw_eq]
  exact normalized_source b

#print axioms normalized_eq
#print axioms canonical_array
#print axioms normalized_source
#print axioms carrier_identity
#print axioms result_identity
#print axioms raw_eq
#print axioms op249_source
end PV_B2_C_GammaSource

end
