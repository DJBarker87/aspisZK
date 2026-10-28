import NBL_AddNative
import NBA_SamplerValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_SamplerReplay
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open ExtractedIndexedAddSmallNatModelV1
open AspisR1GammaCaller.DigitsModel (low_candidate_refines candidateGammaHelpers)
abbrev Bytes32 := Array U8 32#usize
abbrev Words := Array U32 8#usize
abbrev Raw := AspisR1Post25Sampler.field.WideExact
abbrev GammaRaw := AspisR1GammaCaller.field.WideExact

def quotient (q : Words) : U32 := q.val[0]'(by rw [q.property]; decide)

def LowTrace (block : Bytes32) (digits q : Words) : Prop :=
  LPk_Induction.Digits 8 (SamplerBytePass.digits block) (values digits)
    (ExtractedQM31SamplerPassLoop.words q).reverse

theorem low (block : Bytes32) (digits q : Words) (tr : LowTrace block digits q) :
    AspisR1Post25Sampler.sampler.low_base_p_digits block=ok (digits,quotient q) ∧
      Canonical digits ∧ (quotient q).val≤256 := by
  have call := LPk_Result.native_result block digits q tr
  have model := low_candidate_refines block digits (quotient q) call
  refine ⟨call,?_,?_⟩
  · have all : ∀ d∈values digits,d<SamplerMachineBounds.P := by
      rw [model.1]
      exact SamplerNatModel.lowDigits_canonical SamplerMachineBounds.P_pos 8 (SourceSamplerByteRank.rank block)
    intro j hj
    change (digits.val[j]'(by simpa [digits.property] using hj)).val<2147483647
    exact all _ (List.mem_map.mpr ⟨_,List.getElem_mem _,rfl⟩)
  · have bound := (LPk_Induction.eight_digits tr).2.2
    have small : SamplerWordPass.wordValue (ExtractedQM31SamplerPassLoop.words q).reverse < SamplerMachineBounds.B := by
      have width : 256<SamplerMachineBounds.B := by norm_num [SamplerMachineBounds.B]
      omega
    change (q.val[0]'(by rw [q.property]; decide)).val≤256
    rw [LPk_Result.low_word q small]
    exact bound

/-- The ordinary native caller composes its CLOSED low leaf and SAME local
packing observation. No whole ordinary-sample equality is an input. -/
theorem ordinary (block : Bytes32) (digits q : Words) (tr : LowTrace block digits q)
    (raw : Raw) (decode : AspisR1Post25Sampler.sampler.decode8 digits=ok raw) :
    NBA_Installed.actual.sampling.ordinary block=
      ok (AspisR1Post25SamplerPreparedCarrier.candidateToPE raw) := by
  have call := (low block digits q tr).1
  change AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic block=_
  unfold AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic
  unfold AspisR1Post25Sampler.sampler.ordinary_sample
  rw [call,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,decode,bind_tc_ok]

/-- The native increment is checked after the quotient bound has been DERIVED
from the same low trace; no stronger caller input range is imposed. -/
theorem increment (q n : U32) (bound : q.val≤256) (value : n.val=q.val+1) :
    (q+1#u32 : Result U32)=ok n ∧ n.val≤257 := by
  obtain ⟨out,call,cv⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=q) (y:=1#u32) (by scalar_tac))
  have same : out=n := by scalar_tac
  refine ⟨?_,by omega⟩
  simpa only [same] using call

/-- Unwrapped gamma arm; each add is reconstructed from native digit steps. -/
theorem gamma_no_wrap (block : Bytes32) (digits q d1 : Words) (n c1 : U32)
    (tr : LowTrace block digits q) (nv : n.val=(quotient q).val+1)
    (first : NBA_AddCarry.Trace (values digits) n.val (values d1) c1.val)
    (zero : c1=0#u32) (raw : GammaRaw)
    (decode : candidateGammaHelpers.decode d1=ok raw) :
    NBA_Installed.actual.sampling.gamma block=ok (AspisR1ClaimPreparedBridge.gammaToPublic raw) := by
  obtain ⟨lc,canonical,qb⟩ := low block digits q tr
  obtain ⟨inc,nb⟩ := increment (quotient q) n qb nv
  have add := NBL_AddNative.source digits n canonical nb d1 c1 first
  have hlow : candidateGammaHelpers.low block=ok (digits,quotient q) := lc
  have hadd : candidateGammaHelpers.add digits n=ok (false,d1) := by
    change AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p digits n=ok (false,d1)
    simpa only [zero,bne_self_eq_false] using add
  change AspisR1ClaimPreparedBridge.candidateGammaPublic block=_
  unfold AspisR1ClaimPreparedBridge.candidateGammaPublic AspisR1GammaCaller.sampler.gamma_sample
  rw [hlow,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,inc,bind_tc_ok,hadd,Bool.false_eq_true,↓reduceIte,decode]

/-- Wrapped gamma arm. The debug second-carry check is an additional native
obligation; the candidate model's return ignores that Bool. -/
theorem gamma_wrap (block : Bytes32) (digits q d1 d2 : Words) (n c1 c2 : U32)
    (tr : LowTrace block digits q) (nv : n.val=(quotient q).val+1)
    (first : NBA_AddCarry.Trace (values digits) n.val (values d1) c1.val)
    (nonzero : c1≠0#u32)
    (second : NBA_AddCarry.Trace (values d1) 1 (values d2) c2.val)
    (raw : GammaRaw) (decode : candidateGammaHelpers.decode d2=ok raw) :
    NBA_Installed.actual.sampling.gamma block=ok (AspisR1ClaimPreparedBridge.gammaToPublic raw) := by
  obtain ⟨lc,canonical,qb⟩ := low block digits q tr
  obtain ⟨inc,nb⟩ := increment (quotient q) n qb nv
  have add := NBL_AddNative.source digits n canonical nb d1 c1 first
  have add2 := NBL_AddNative.source d1 1#u32 (NBL_AddNative.canonical digits n d1 c1 first)
    (by decide) d2 c2 second
  have hlow : candidateGammaHelpers.low block=ok (digits,quotient q) := lc
  have hadd : candidateGammaHelpers.add digits n=ok (true,d1) := by
    change AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p digits n=ok (true,d1)
    simpa only [bne_iff_ne.mpr nonzero] using add
  have hadd2 : candidateGammaHelpers.add d1 1#u32=ok (c2 != 0#u32,d2) := add2
  change AspisR1ClaimPreparedBridge.candidateGammaPublic block=_
  unfold AspisR1ClaimPreparedBridge.candidateGammaPublic AspisR1GammaCaller.sampler.gamma_sample
  rw [hlow,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,inc,bind_tc_ok,hadd,↓reduceIte,hadd2,decode]

#print axioms low
#print axioms ordinary
#print axioms increment
#print axioms gamma_no_wrap
#print axioms gamma_wrap
end AspisR1.NBL_SamplerReplay
end
