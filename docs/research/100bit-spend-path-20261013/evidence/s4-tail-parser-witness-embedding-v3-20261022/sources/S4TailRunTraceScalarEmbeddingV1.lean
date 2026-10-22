import S4TailParserWitnessEmbeddingV1
import S4TailTraceMemberWitnessV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsTailRunTraceScalarEmbeddingV1

abbrev Ops := AspisR1FastDotsActualCallbackTailTraceRootV1.Ops
abbrev Wide := AspisR1FastDotsActualCallbackTailTraceRootV1.Wide
abbrev Tail := AspisR1FastDotsActualCallbackTailTraceRootV1.Tail
abbrev Range := AspisR1FastDotsActualTailBodyTraceRootV1.Range
abbrev Contribution := AspisR1FastDotsActualTailBodyTraceRootV1.Contribution
abbrev C1 := AspisR1.MixedLeafEncoding.C1
abbrev C2 := AspisR1.MixedLeafEncoding.C2

/-- Every actual C2 scalar emitted in the successful 0..2 tail trace is
identified with the same slot/lane in the canonical C2 opening. The witness is
recovered from the trace itself; no independent read, slice, or parse premise
is supplied per contribution. -/
theorem run_trace_scalar_embeddings
    (ops : Ops) (a : Array Aeneas.Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (slotFin : Fin 4) (old out : Tail) (cs : List Contribution)
    (c1 : C1) (c2 : C2)
    (hslot : slot.val = slotFin.val)
    (hopening : a.val.map AspisR1.ExtractedRecordByteValue.rawByte =
      AspisR1.MixedLeafEncoding.encodeC1 c1 ++ AspisR1.MixedLeafEncoding.encodeC2 c2)
    (hbinding : ops.qm31FromBytes = AspisR1FastDotsCurrentQmParserRootV1.parser)
    (htrace : AspisR1FastDotsActualTailLoopTraceRootV1.RunTrace ops a g slot
      {start:=0#usize, «end»:=2#usize} old out cs) :
    ∀ c ∈ cs, ∃ termFin : Fin 2, termFin.val = c.term.val ∧
      AspisR1FastDotsTailLiteralProductsRootV1.embedQM c.scalar =
        algebraMap AspisV8R15.ExactTowerBase.QM31Exact AspisWideTower.WideExact
          ((c2 slotFin) termFin) := by
  have hmember := AspisR1.S4TailTraceMemberWitnessV1.trace_member_input_witness
    ops a g slot _ old out cs htrace
  have hterm := AspisR1.S4TailTraceMemberWitnessV1.trace_member_term_lt_two
    ops a g slot old out cs htrace
  intro c hc
  obtain ⟨before,after,s0,s1,hw⟩ := hmember c hc
  let termFin : Fin 2 := ⟨c.term.val, hterm c hc⟩
  refine ⟨termFin, rfl, ?_⟩
  exact AspisR1FastDotsTailParserEmbeddingV1.contribution_exact_embedding
    ops a g slot slotFin termFin before after s0 s1 c c1 c2
    hslot rfl hopening hbinding hw

#print axioms run_trace_scalar_embeddings
end AspisR1FastDotsTailRunTraceScalarEmbeddingV1
