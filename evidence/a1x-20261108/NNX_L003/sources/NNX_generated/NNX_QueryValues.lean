import NNU_QueryValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_QueryValues
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
structure Slots (g h : Ops) : Prop extends NNU_QueryLoops.Slots g h where
 op0 : @g.op0 = @h.op0
 op11 : g.op11 = h.op11
 line : g.op16 = h.op16
 circle : g.op17 = h.op17
 geometry : g.op18 = h.op18
 dots : g.op20 = h.op20
 decode : g.op21 = h.op21
 equality : g.widePartialEq = h.widePartialEq
 phase : ∀ ph, g.op19 none ph = h.op19 none ph
 sum : ∀ x y, g.op2 x y = h.op2 x y
 product : ∀ x q, NBF_PowerStep.Canonical q → g.op3 x q = h.op3 x q
 power : ∀ x y, g.op9 x y = h.op9 x y

theorem accumulate (g h : Ops) (s : Slots g h)
 (p : verifier.Prepared) (a : verifier.Accumulator) (node : U32)
 (value : aspis_core.field.wide_exact.WideExact) (pending : verifier.BatchedWeights)
 (hq : NBF_PowerStep.Canonical a.power) :
 verifier.accumulate_batched_with_node g p a node value pending =
 verifier.accumulate_batched_with_node h p a node value pending := by
 unfold verifier.accumulate_batched_with_node
 simp only [s.zero,s.one,NNU_QueryLoops.basisLoop _ _ s.toSlots,
  NNU_QueryLoops.rowLoop _ _ s.toSlots,s.product value a.power hq,s.sum,s.power,s.trace]

theorem source (g h : Ops) (s : Slots g h) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geo : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (hq : NBF_PowerStep.Canonical a.power) :
 verifier.candidate.query_values g proof p a scratch none geo pending =
 verifier.candidate.query_values h proof p a scratch none geo pending := by
 unfold verifier.candidate.query_values
 simp only [s.op11,s.dots,s.trace,s.geometry,s.circle,s.op0,
  NNU_QueryValues.callback _ _ s.decode,s.equality,s.line,s.mul,s.double,s.one,s.sub,
  accumulate g h s p a _ _ pending hq,s.phase]
#print axioms accumulate
#print axioms source
end AspisR1.NNX_QueryValues
end
