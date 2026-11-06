import NKE_CommonSource
import NKE_PendingNative
import NKE_FlushNative
import NKE_LogPrefix
set_option autoImplicit false
noncomputable section
namespace NKE_CommonNative
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
abbrev K := aspis_core.field.QM31
abbrev Row := Port3_NativePendingBody.Row

def zeros (weights : Slice K) : alloc.vec.Vec Row :=
 ⟨List.replicate weights.val.length (Array.repeat 4#usize 0#u64),by simpa using weights.property⟩

def pendingG (r : NP6_StdModel.Reservation) (weights : Slice K) : R verifier.BatchedWeights :=
 match r with
 | .Err _ => ok (.Err .Allocation)
 | .Ok () => ok (.Ok ⟨NKE_PendingNative.states weights (zeros weights) 64,0#usize⟩)

/-- Selected native windows, instantiated at the actual event arguments.
The guard marks the reviewed native domain; outside it this partial transform
retains the original event, and earns no native credit there. -/
def event (r : NP6_StdModel.Reservation) : Event → Event
 | .pending weights reply =>
   .pending weights (if weights.val.length=64 then pendingG r weights else reply)
 | .flush pending weights reply =>
   .flush pending weights (if pending.raw.val.length=64 ∧ weights.val.length=64
    then ok (NJJ_Flush.output pending) else reply)
 | .query proof p a g geometry pending reply =>
   .query proof p a g geometry pending (NKE_QueryReturn.observed reply)
 | e => e

theorem event_exact (r : NP6_StdModel.Reservation) (e : Event)
 (clause : NKE_CommonClauses.Clause r e) : event r e=e := by
 cases e with
 | pending weights reply =>
  change reply=NJJ_Common.pending r weights at clause
  change Event.pending weights (if weights.val.length=64 then pendingG r weights else reply)=_
  by_cases width : weights.val.length=64
  · rw [if_pos width]
    have same : NJJ_Common.pending r weights=pendingG r weights := by
     have original := NKE_PendingNative.source r weights (zeros weights) width
      (by simpa only [zeros,List.length_replicate] using width)
     cases r with
     | Err e => exact original
     | Ok unit => cases unit;exact original
    rw [←same,clause]
  · rw [if_neg width]
 | flush pending weights reply =>
  change reply=Port3_FlushInstall.flush pending weights at clause
  change Event.flush pending weights (if pending.raw.val.length=64 ∧ weights.val.length=64
   then ok (NJJ_Flush.output pending) else reply)=_
  by_cases width : pending.raw.val.length=64 ∧ weights.val.length=64
  · rw [if_pos width,clause,NJJ_Flush.source pending weights width.1 width.2]
  · rw [if_neg width]

 | query proof p a g geometry pending reply =>
  change Event.query proof p a g geometry pending (NKE_QueryReturn.observed reply)=_
  rw [NKE_QueryReturn.observed_exact]
 | resume ck proof pub reply => rfl
 | powers gamma reply => rfl
 | inactive bytes reply => rfl
 | merkle proof p root reply => rfl
 | geometry queries next reply => rfl
 | finish v p a reply => rfl

/-- Fold retains exact ordered event carriers and full returning/abort replies.
It normalizes only the three reviewed window families, not the whole parent. -/
def G (r : NP6_StdModel.Reservation) (before : List Event) (log : List Event) : List Event :=
 NKE_LogPrefix.G (fun state e=>state++[event r e]) before log

theorem fold (r : NP6_StdModel.Reservation) (before log : List Event)
 (clauses : ∀ e∈log,NKE_CommonClauses.Clause r e) : G r before log=before++log := by
 induction log generalizing before with
 | nil => simp only [G,NKE_LogPrefix.G,List.foldl_nil,List.append_nil]
 | cons e tail ih =>
  change G r (before++[event r e]) tail=before++(e::tail)
  rw [event_exact r e (clauses e (by simp)),ih]
  · simp only [List.append_assoc,List.singleton_append]
  · intro e he;exact clauses e (List.mem_cons_of_mem _ he)

/-- The SAME source log supplies every clause internally, including its exact
rejected prefix. No independently selected native log is assumed. -/
theorem actual (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 let log := (run wr rr merkle finish d pub proof ck hash none).events
 G rr [] log=log := by
 dsimp only
 simpa only [List.nil_append] using
  fold rr [] _ (NKE_CommonSource.clauses wr rr merkle finish d pub proof ck hash)

#print axioms event_exact
#print axioms fold
#print axioms actual
end NKE_CommonNative
