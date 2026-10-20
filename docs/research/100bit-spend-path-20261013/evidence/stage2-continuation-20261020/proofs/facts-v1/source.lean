import Stage2ContinuationParse
import Stage2ContinuationResume
import Stage2ContinuationQueryAdvance
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2
abbrev stage2QueryCall (aops : AccumulateOps) (ops : QueryOps) : QueryCall :=
  fun proof p a g obs geometry b =>
    verifier.candidate.queryWithOps aops ops proof p a g obs geometry b

/-- No query-increment hypothesis is needed: it follows from the complete
emitted query and accumulation bodies with arbitrary typed backend operations. -/
theorem stage2_twelve_ordered_calls (aops : AccumulateOps) (ops : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (g : Array Stage2E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (start : a.next.val = 10)
    (h : verifier.candidate.query_loop (stage2QueryCall aops ops)
      proof p a g obs geometry b 22#usize = ok (.Ok (out,bout))) :
    Stage2ContinuationLoop.Chain (fun a : verifier.Accumulator => a.next.val)
      (Stage2ContinuationOwnedLoop.adapt
        (fun a b => stage2QueryCall aops ops proof p a g obs geometry b))
      a b out bout 12 := by
  apply emitted_twelve_ordered_calls _ proof p g obs geometry ?_ a out b bout start h
  intro a a1 b b1 hc
  exact query_next aops ops proof p a a1 g obs geometry b b1 hc

#print axioms stage2_twelve_ordered_calls
#print axioms AspisR1Stage2ContinuationParse.successful_length
#print axioms resume_rehash_checkpoint_field
end AspisR1Stage2
