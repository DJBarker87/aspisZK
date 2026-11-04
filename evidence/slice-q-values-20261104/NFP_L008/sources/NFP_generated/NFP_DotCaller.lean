import NFP_DotInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_DotCaller
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody NFP_QueryCuts NFP_DotInstall
/-- Dot substitution cannot change any later callback, error, state or
phase effect. The complete partial Result is retained. -/
theorem tail (ops : Ops) (qPlace gPlace : Nat) (p : verifier.Prepared)
 (a : verifier.Accumulator) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (u : Usize) (q : Slice U8) (dots : Dots) :
 NFP_QueryCuts.tail (oracle ops qPlace gPlace) p a geometry pending u q dots =
 NFP_QueryCuts.tail (cohort ops) p a geometry pending u q dots := by rfl

theorem query (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize)
 (qPlace gPlace : Nat) (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g))
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) :
 verifier.candidate.query_values (oracle ops qPlace gPlace) proof p a g none geometry pending =
 verifier.candidate.query_values (cohort ops) proof p a g none geometry pending := by
 rw [NFP_QueryCuts.source,NFP_QueryCuts.source,NFP_DotInstall.head ops proof p a g qPlace gPlace canonical]
 congr 1
 funext packet
 rcases packet with ⟨u,q,dots⟩
 exact tail ops qPlace gPlace p a geometry pending u q dots
#print axioms tail
#print axioms query
end AspisR1.NFP_DotCaller
end
