import S1QueryProgramRelationV1
import S1QueryPairedBindV1
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result
open PreparedHashCode PreparedHashCode.QueryPair
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open AspisR1CurrentCaller.BorrowedClaimPrepared AspisS1QueryProgramRelation

/-- Accepted terminal relation preserves the full source transcript hash,
the ordered query list and selected state. No condition is imposed on source
rejection/fail/div; no probability conditioning on acceptance is performed. -/
def AcceptedQueryRelation {H : Type} (hash : H)
    (source : Result (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H))
    (model : Except Nat (List Nat) × State) : Prop :=
  ∀ queries after,source=ok (.Ok queries,after) →
    model=(.ok (queries.val.map (fun w => w.val)),decodeState after.state) ∧ after.hash=hash

theorem source_leaf_related {H : Type} (D : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (absorbed : State) (bs xs : List State) (hbs : bs.length=8) (hxs : xs.length=8) :
    AcceptedQueryRelation self.hash (sourceQueryLeaf D {self with state:=encodeState absorbed} bs xs)
      (R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0 bs xs absorbed) := by
  intro queries after success
  obtain ⟨blocks,advances,hpack,hblocks,hadvances⟩ := packEight_exact bs xs hbs hxs
  unfold sourceQueryLeaf at success
  rw [hpack] at success
  obtain ⟨selected,hdecode,hafter⟩ := finish_accepted closedHashQueries D
    {self with state:=encodeState absorbed} after blocks advances queries success
  change Query31ConcreteMaterializedSchedule.actualConcreteDecode
    Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances=ok (.Ok (queries,selected)) at hdecode
  have decoded := Query31ConcreteMaterializedSchedule.adaptScanResult_success hdecode
  have scanned := AspisS1QueryScanModel.default_driver_scanOut blocks advances queries selected absorbed decoded
  rw [hblocks,hadvances] at scanned
  rw [hafter]
  exact ⟨scanned,rfl⟩

/-- Concrete structural source-to-fixed-query refinement, for EVERY sequence
of replies, with exact same reads. No scanner-law or oracle-interpretation
premise remains. This is the source-shaped reference, not native SDK closure. -/
theorem closed_query31_same_reads {H M Cv : Type} {L : Nat} (p : FS2.Duplex.Params M Cv L)
    (D : aspis_core.Digest32 H) (self : transcript.Transcript H) (payload : Slice U8) :
    SameReads (AcceptedQueryRelation self.hash)
      (oracleProgram (PreparedQueryEffects.queries effects closedHashQueries D self 31#u8 payload))
      (fixedQuery31 self.state payload) := by
  rw [query31_program_paired p]
  unfold fixedQuery31
  apply SameReads.ask
  intro absorbed
  apply paired_related
  intro bs xs hbs hxs
  apply source_leaf_related D self absorbed bs xs
  · simpa using hbs
  · simpa using hxs

#print axioms source_leaf_related
#print axioms closed_query31_same_reads
end AspisR1PublicPreparation.PreparedQueryMaterialize
