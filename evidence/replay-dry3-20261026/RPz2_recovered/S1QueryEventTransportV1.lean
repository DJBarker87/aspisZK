import S1QueryClosedRelationV1
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result
open PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open AspisR1CurrentCaller.BorrowedClaimPrepared AspisS1QueryProgramRelation
abbrev QueryEvent := List (Bytes × State) → List Nat → State → Bool

def sourceQueryEvent {H : Type} (event : QueryEvent)
    (view : View Bytes State (Result (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H))) : ℚ :=
  match view.2 with
  | .ok (.Ok queries,after) => if event view.1 (queries.val.map (fun w => w.val)) (decodeState after.state) then 1 else 0
  | _ => 0

def fixedQueryEvent (event : QueryEvent) (view : View Bytes State (Except Nat (List Nat) × State)) : ℚ :=
  match view.2.1 with
  | .ok queries => if event view.1 queries view.2.2 then 1 else 0
  | .error _ => 0

private theorem fixedEvent_nonnegative (event : QueryEvent)
    (view : View Bytes State (Except Nat (List Nat) × State)) : 0≤fixedQueryEvent event view := by
  unfold fixedQueryEvent
  split
  · split <;> norm_num
  · exact le_rfl

theorem related_event_le {H : Type} (hash : H) (event : QueryEvent) (log : List (Bytes × State))
    (source : Result (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H))
    (model : Except Nat (List Nat) × State) (related : AcceptedQueryRelation hash source model) :
    sourceQueryEvent event (log,source)≤fixedQueryEvent event (log,model) := by
  cases source with
  | fail e => exact fixedEvent_nonnegative event _
  | div => exact fixedEvent_nonnegative event _
  | ok pair =>
    rcases pair with ⟨result,after⟩
    cases result with
    | Err e => exact fixedEvent_nonnegative event _
    | Ok queries =>
      obtain ⟨modelEq,hashEq⟩ := related queries after rfl
      rw [modelEq]
      exact le_rfl

/-- Unconditioned bad-event domination for independent answers. The event
may inspect the COMPLETE ordered log, ordered queries and selected state. -/
theorem closed_query31_independent_event_le {H M Cv : Type} {L : Nat}
    (p : FS2.Duplex.Params M Cv L) (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (payload : Slice U8) (event : QueryEvent) :
    independentMean (oracleProgram (PreparedQueryEffects.queries effects closedHashQueries D self 31#u8 payload))
      (sourceQueryEvent event) ≤ independentMean (fixedQuery31 self.state payload) (fixedQueryEvent event) := by
  apply (closed_query31_same_reads p D self payload).independentMean_le
  intro log source model related
  exact related_event_le self.hash event log source model related

/-- The same event domination for memoized byte-oracle execution with any
initial cache. This does not assume fresh replies on repeated reads. -/
theorem closed_query31_memoized_event_le {H M Cv : Type} {L : Nat}
    (p : FS2.Duplex.Params M Cv L) (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (payload : Slice U8) (table : Table Bytes State) (event : QueryEvent) :
    lazyMean (oracleProgram (PreparedQueryEffects.queries effects closedHashQueries D self 31#u8 payload))
      table (sourceQueryEvent event) ≤ lazyMean (fixedQuery31 self.state payload) table (fixedQueryEvent event) := by
  apply (closed_query31_same_reads p D self payload).lazyMean_le table
  intro log source model related
  exact related_event_le self.hash event log source model related

#print axioms related_event_le
#print axioms closed_query31_independent_event_le
#print axioms closed_query31_memoized_event_le
end AspisR1PublicPreparation.PreparedQueryMaterialize
