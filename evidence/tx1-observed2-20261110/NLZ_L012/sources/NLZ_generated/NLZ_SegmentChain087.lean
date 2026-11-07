import NLZ_Resources
import NLR_PrepareFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLZ_Segments087
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NLZ_Resources
structure State where
 machine : NLJ_Prepare.State Unit
 heap : Heap
/-- Support relation only. A native segment certificate must supply the
canonical source-step equation AND its complete physical transition. The
same heap is threaded between every two consecutive cuts, not chosen later.
Resource effects are retained explicitly; their source-site interpretation
remains an OPEN obligation, so this relation is never a row root. -/
inductive Chain (cfg : NLJ_Prepare.Configuration) : Nat → State → Result (NLJ_Prepare.Out) →
 PreparedHashCode.Log → List NLJ_Prepare.Event → List Effect → Heap → Prop where
 | returned {n s out log effects heap}
   (value : PreparedHashCode.run (NLJ_Prepare.step cfg s.machine) = (log,ok (.inl out)))
   (physical : Occurrence) (before : physical.before = s.heap)
   (after : physical.after = heap) (trace : physical.effects = effects) :
   Chain cfg (n+1) s (ok out) log [NLJ_Prepare.event s.machine] effects heap
 | fail {n s error log effects heap}
   (value : PreparedHashCode.run (NLJ_Prepare.step cfg s.machine) = (log,fail error))
   (physical : Occurrence) (before : physical.before = s.heap)
   (after : physical.after = heap) (trace : physical.effects = effects) :
   Chain cfg (n+1) s (fail error) log [NLJ_Prepare.event s.machine] effects heap
 | div {n s log effects heap}
   (value : PreparedHashCode.run (NLJ_Prepare.step cfg s.machine) = (log,div))
   (physical : Occurrence) (before : physical.before = s.heap)
   (after : physical.after = heap) (trace : physical.effects = effects) :
   Chain cfg (n+1) s div log [NLJ_Prepare.event s.machine] effects heap
 | next {n s after out log suffix events effects rest heap}
   (value : PreparedHashCode.run (NLJ_Prepare.step cfg s.machine) = (log,ok (.inr after.machine)))
   (physical : Occurrence) (before : physical.before = s.heap)
   (post : physical.after = after.heap) (trace : physical.effects = effects)
   (tail : Chain cfg n after out suffix events rest heap) :
   Chain cfg (n+1) s out (log ++ suffix) (NLJ_Prepare.event s.machine :: events)
    (effects ++ rest) heap
/-- Every value/error/abort source prefix projects from one resource chain.
This does NOT construct the physical segment certificates. -/
theorem source (cfg : NLJ_Prepare.Configuration) {n : Nat} {s : State} {out : Result (NLJ_Prepare.Out)}
 {log : PreparedHashCode.Log} {events : List NLJ_Prepare.Event}
 {effects : List Effect} {heap : Heap}
 (chain : Chain cfg n s out log events effects heap) :
 NLJ_Prepare.Invocation cfg n s.machine out log events := by
 induction chain with
 | returned value _ _ _ _ => exact .returned value
 | fail value _ _ _ _ => exact .fail value
 | div value _ _ _ _ => exact .div value
 | next value _ _ _ _ _ ih => exact .next value ih
/-- Conditional fold only; no weaker136 packet is used. Each source-step
premise, especially137/179, still needs the complete native child certificate. -/
theorem fold (cfg : NLJ_Prepare.Configuration) {i : NLJ_Prepare.Input Unit} {before after : Heap}
 {out : Result (NLJ_Prepare.Out)} {log : PreparedHashCode.Log}
 {events : List NLJ_Prepare.Event} {effects : List Effect}
 (chain : Chain cfg 12 ⟨NLJ_Prepare.initial i,before⟩ out log events effects after) :
 PreparedHashCode.run (AspisR1CurrentCaller.SdkD_PrepareSource.code cfg.base cfg.boundaries cfg.std
  i.digest i.publicValue i.proof i.hash i.scratch) = (log,out) := by
 exact NLR_Prepare.source_fold cfg i out log events (source cfg chain)
#print axioms source
#print axioms fold
#print fold
end AspisR1.NLZ_Segments087
end
