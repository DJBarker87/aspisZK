import NLZ_Resources
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLZ_Segments137
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NLZ_Resources
structure State where
 machine : NLJ_Observed.State Unit
 heap : Heap
/-- Support relation only. A native segment certificate must supply the
canonical source-step equation AND its complete physical transition. The
same heap is threaded between every two consecutive cuts, not chosen later.
Resource effects are retained explicitly; their source-site interpretation
remains an OPEN obligation, so this relation is never a row root. -/
inductive Chain : Nat → State → Result (NLJ_Observed.Out Unit) →
 PreparedHashCode.Log → List NLJ_Observed.Event → List Effect → Heap → Prop where
 | returned {n s out log effects heap}
   (value : PreparedHashCode.run (NLJ_Observed.step s.machine) = (log,ok (.inl out)))
   (physical : Occurrence) (before : physical.before = s.heap)
   (after : physical.after = heap) (trace : physical.effects = effects) :
   Chain (n+1) s (ok out) log [NLJ_Observed.event s.machine] effects heap
 | fail {n s error log effects heap}
   (value : PreparedHashCode.run (NLJ_Observed.step s.machine) = (log,fail error))
   (physical : Occurrence) (before : physical.before = s.heap)
   (after : physical.after = heap) (trace : physical.effects = effects) :
   Chain (n+1) s (fail error) log [NLJ_Observed.event s.machine] effects heap
 | div {n s log effects heap}
   (value : PreparedHashCode.run (NLJ_Observed.step s.machine) = (log,div))
   (physical : Occurrence) (before : physical.before = s.heap)
   (after : physical.after = heap) (trace : physical.effects = effects) :
   Chain (n+1) s div log [NLJ_Observed.event s.machine] effects heap
 | next {n s after out log suffix events effects rest heap}
   (value : PreparedHashCode.run (NLJ_Observed.step s.machine) = (log,ok (.inr after.machine)))
   (physical : Occurrence) (before : physical.before = s.heap)
   (post : physical.after = after.heap) (trace : physical.effects = effects)
   (tail : Chain n after out suffix events rest heap) :
   Chain (n+1) s out (log ++ suffix) (NLJ_Observed.event s.machine :: events)
    (effects ++ rest) heap
/-- Every value/error/abort source prefix projects from one resource chain.
This does NOT construct the physical segment certificates. -/
theorem source {n : Nat} {s : State} {out : Result (NLJ_Observed.Out Unit)}
 {log : PreparedHashCode.Log} {events : List NLJ_Observed.Event}
 {effects : List Effect} {heap : Heap}
 (chain : Chain n s out log events effects heap) :
 NLJ_Observed.Invocation n s.machine out log events := by
 induction chain with
 | returned value _ _ _ _ => exact .returned value
 | fail value _ _ _ _ => exact .fail value
 | div value _ _ _ _ => exact .div value
 | next value _ _ _ _ _ ih => exact .next value ih
/-- Conditional fold only; no weaker136 packet is used. Each source-step
premise, especially136, still needs the complete native child certificate. -/
theorem fold {i : NLJ_Observed.Input Unit} {before after : Heap}
 {out : Result (NLJ_Observed.Out Unit)} {log : PreparedHashCode.Log}
 {events : List NLJ_Observed.Event} {effects : List Effect}
 (chain : Chain 6 ⟨NLJ_Observed.initial i,before⟩ out log events effects after) :
 PreparedHashCode.run (S1SemanticCode.verify
  (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation))
  i.digest i.publicValue i.bytes i.hash none) = (log,out) := by
 exact NLJ_Observed.events_from_cuts i out log events (source chain)
#print axioms source
#print axioms fold
#print fold
end AspisR1.NLZ_Segments137
end
