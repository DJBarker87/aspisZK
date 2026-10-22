import D18S4Width29LiteralJoinCheckV1
import S4HeadCodecProjectionV2
import S4TailCoefficientPowersV1
import S4TailParserWitnessEmbeddingV1
import S4TailTraceMemberWitnessV1
import S4ConcreteKernelOpsRootV1
import R1LiteralTypedWords
import R1ExactBaseProjection
import R1MixedLeafEncoding

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1D18S4ConcreteWidth29KernelV1

open AspisR1D18S4Width29LiteralJoinV1
open AspisR1FastDotsLiteralCallbackValueRootV1
open AspisR1FastDotsLiteralHeadSumRootV1
open AspisR1FastDotsTailFieldProductRootV1
open AspisR1FastDotsTailLiteralProductsRootV1
open AspisR1FastDotsActualTailLoopTraceRootV1
open AspisR1FastDotsActualTailBodyTraceRootV1 (Contribution)
open AspisR1FastDotsHeadTailSharedWitnessRootV2
open AspisR1.MixedLeafEncoding
open AspisV8R15.ExactTowerBase

abbrev Ops := AspisR1FastDotsQueryValuesFourCallbackFieldResultV2.Ops
abbrev Wide := AspisR1FastDotsLiteralHeadSumRootV1.Wide
abbrev TowerWide := AspisR1FastDotsTailFieldProductRootV1.TowerWide
abbrev Contribution := AspisR1FastDotsActualTailBodyTraceRootV1.Contribution
abbrev Range := core.ops.range.Range Usize

def localWord (c1 : C1) (c2 : C2) (slot : Fin 4) : Fin 29 → TowerWide :=
  fun lane => AspisR1.LiteralTypedWords.word AspisR1.ExactBaseProjection.embed
    (algebraMap QM31Exact TowerWide) (fun _ => c1 slot) (fun _ => c2 slot) lane
    (0 : Fin 1048576)

/-- A successful concrete callback result is the width-29 batch value for
its exact C1/C2 source opening.  The callback's first parser result and both
actual tail parser results are projected internally; no per-term scalar,
coefficient, or successful-child premise is assumed. -/
theorem literal_field_result_concrete_width29
    (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slotU : Usize) (slot : Fin 4) (value : Wide) (gamma : TowerWide)
    (c1 : C1) (c2 : C2)
    (hslot : slotU.val = slot.val)
    (hbytes : a.val.map AspisR1.ExtractedRecordByteValue.rawByte =
      encodeC1 c1 ++ encodeC2 c2)
    (hpowers : ∀ j : Fin 29,
      AspisR1FastDotsTailFieldProductRootV1.wideDecoded
        (g.val[j.val]'(by scalar_tac)) = gamma ^ j.val)
    (hresult : LiteralFieldResult
      (AspisR1FastDotsForwardLiteralValueRootV1.literalOps
        AspisR1FastDotsConcreteKernelOpsRootV1.concreteOps)
      a g slotU value) :
    AspisR1CurrentWide.Proof.decodeWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE value) =
      AspisV6Width29CorrelatedAgreement.width29Batch
        (localWord c1 c2 slot) gamma := by
  let ops : Ops := AspisR1FastDotsForwardLiteralValueRootV1.literalOps
    AspisR1FastDotsConcreteKernelOpsRootV1.concreteOps
  rcases hresult with ⟨wide28,q,tailStart,tail2,cs,hfirstQuery,hg28,hrun,
    haccepted,hdecode⟩
  have hheadFin := AspisR1S4HeadCodecProjectionV2.c1_m31_head_term_fin26
    c1 c2 g slot gamma hbytes hpowers
  have hhead : ∀ (n : Nat) (hn : n < 26),
      headTermValue a g slotU.val n = localWord c1 c2 slot ⟨n, by omega⟩ * gamma ^ n := by
    intro n hn
    let j : Fin 26 := ⟨n, hn⟩
    have h := hheadFin j
    rw [hslot]
    simpa [localWord, AspisR1.LiteralTypedWords.word, j,
      AspisR1.ExactBaseProjection.embed, hn] using h
  have hwide28 : ∀ wide28 : Wide,
      Array.index_usize g 28#usize = .ok wide28 →
        AspisR1FastDotsTailFieldProductRootV1.wideDecoded wide28 = gamma ^ 28 := by
    intro x hget
    exact AspisR1.S4TailCoefficientPowersV1.index_success_power
      g 28#usize x gamma hpowers hget
  have hbinding : ops.qm31FromBytes =
      AspisR1FastDotsCurrentQmParserRootV1.parser := by rfl
  have hfirst : ∀ w q' ts t2 cs',
      FirstQueryInput ops a slotU q' →
      Array.index_usize g 28#usize = .ok w →
      RunTrace ops a g slotU {start:=0#usize, «end»:=2#usize} ts t2 cs' →
      AspisR1FastDotsTailLiteralProductsRootV1.embedQM q' =
        localWord c1 c2 slot ⟨28, by decide⟩ := by
    intro w q' ts t2 cs' hq _hget _htrace
    have he := AspisR1FastDotsTailParserEmbeddingV1.first_query_exact_embedding
      ops a slotU slot q' c1 c2 (by omega) hbytes hbinding hq
    simpa [localWord, AspisR1.LiteralTypedWords.word,
      AspisR1.ExactBaseProjection.embed] using he
  have htail : ∀ ts t2 cs',
      RunTrace ops a g slotU {start:=0#usize, «end»:=2#usize} ts t2 cs' →
      ∀ (c : Contribution) (hc : c ∈ cs') (hterm : c.term.val < 3),
        AspisR1FastDotsTailFieldProductRootV1.wideDecoded c.coefficient =
            gamma ^ (26+c.term.val) ∧
          AspisR1FastDotsTailLiteralProductsRootV1.embedQM c.scalar =
            localWord c1 c2 slot ⟨26+c.term.val, by omega⟩ := by
    intro ts t2 cs' htrace c hc hterm
    have hcoefficient := AspisR1.S4TailCoefficientPowersV1.tail_trace_coefficient_powers
      ops a g slotU {start:=0#usize, «end»:=2#usize} ts t2 cs' gamma hpowers htrace c hc
    obtain ⟨iter,iter',s0,s1,hwitness⟩ :=
      AspisR1.S4TailTraceMemberWitnessV1.trace_member_input_witness
        ops a g slotU {start:=0#usize, «end»:=2#usize} ts t2 cs' htrace c hc
    have hterm2 : c.term.val < 2 :=
      AspisR1.S4TailTraceMemberWitnessV1.trace_member_term_lt_two
        ops a g slotU ts t2 cs' htrace c hc
    let termFin : Fin 2 := ⟨c.term.val,hterm2⟩
    have hembed := AspisR1FastDotsTailParserEmbeddingV1.contribution_exact_embedding
      ops a g slotU slot termFin iter iter' s0 s1 c c1 c2
      (by omega) rfl hbytes hbinding hwitness
    have htermval : c.term.val = 0 ∨ c.term.val = 1 := by omega
    constructor
    · exact hcoefficient
    · rcases htermval with hzero | hone
      · simpa [localWord, AspisR1.LiteralTypedWords.word, termFin, hzero,
          AspisR1.ExactBaseProjection.embed] using hembed
      · simpa [localWord, AspisR1.LiteralTypedWords.word, termFin, hone,
          AspisR1.ExactBaseProjection.embed] using hembed
  exact AspisR1D18S4Width29LiteralJoinV1.literal_field_result_width29
    ops a g slotU value gamma (localWord c1 c2 slot)
    ⟨wide28,q,tailStart,tail2,cs,hfirstQuery,hg28,hrun,haccepted,hdecode⟩
    hhead hwide28 hfirst htail

#print axioms literal_field_result_concrete_width29
#print axioms AspisR1S4HeadCodecProjectionV2.c1_m31_head_term_fin26
#print axioms AspisR1FastDotsTailParserEmbeddingV1.first_query_exact_embedding
#print axioms AspisR1FastDotsTailParserEmbeddingV1.contribution_exact_embedding
#print axioms AspisR1.S4TailCoefficientPowersV1.tail_trace_coefficient_powers
#print axioms AspisR1D18S4Width29LiteralJoinV1.literal_field_result_width29
end AspisR1D18S4ConcreteWidth29KernelV1
