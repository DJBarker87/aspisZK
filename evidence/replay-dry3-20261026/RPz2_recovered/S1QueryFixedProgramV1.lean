import S1QueryFinishAcceptedV1
import S1QueryPairEvaluationV1
import S1QueryPackEightExactV1
import S1QueryScanDriverModelV1
import S1QueryRow31ProgramV1
import S1ClosedPreparationHashCodeV1
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open PreparedHashCode PreparedHashCode.QueryPair
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps
open AspisR1CurrentCaller.BorrowedClaimPrepared

/-- Fixed causal byte-oracle query program. It has no source decoder/embed or
hash callback: the same full mathematical eight-pair sampler determines its
ordered query result and selected state. The absorb address is literal source
framing; its separate bounded frozen Addr interpretation is not asserted here. -/
def fixedQuery31 (state : Bytes32) (payload : Slice U8) :
    Program Bytes State (Except Nat (List Nat) × State) :=
  .ask (flatten (CallerStep.openingAbsorbParts state 191#u8
    (UScalar.cast .U32 (Slice.len payload)) payload)) fun absorbed =>
      pairedBytesProgram (fun bs xs => R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0 bs xs absorbed)
        8 absorbed [] []

theorem modelMaterialize_eq_paired {M Cv : Type} {L : Nat} (p : Params M Cv L) (state : Bytes32) :
    modelMaterialize p state=pairedBytesProgram packEight 8 (decodeState state) [] [] :=
  (pairedBytesProgram_eq_model p packEight 8 (decodeState state) [] []).symm

/-- All source outcomes have the same complete ordered log as the fixed
mathematical program. Accepted source outcomes additionally agree on queries
and selected state; the full source transcript hash is preserved as well. -/
theorem closed_query31_fixed_program {H M Cv : Type} {L : Nat}
    (p : Params M Cv L) (D : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (payload : Slice U8) (oracle : Bytes → State) :
    (eval oracle (oracleProgram (PreparedQueryEffects.queries effects closedHashQueries D self 31#u8 payload))).1=
      (eval oracle (fixedQuery31 self.state payload)).1 ∧
    ∀ (queries : Array U32 22#usize) (after : transcript.Transcript H),
      (eval oracle (oracleProgram (PreparedQueryEffects.queries effects closedHashQueries D self 31#u8 payload))).2=
        ok (.Ok queries,after) →
      (eval oracle (fixedQuery31 self.state payload)).2=
        (.ok (queries.val.map (fun w => w.val)),decodeState after.state) ∧ after.hash=self.hash := by
  let address := flatten (CallerStep.openingAbsorbParts self.state 191#u8
    (UScalar.cast .U32 (Slice.len payload)) payload)
  let absorbed := oracle address
  obtain ⟨log,bs,xs,hbs,hxs,heval⟩ := paired_eval_witness 8 absorbed [] [] oracle
  have blen : bs.length=8 := by simpa using hbs
  have xlen : xs.length=8 := by simpa using hxs
  obtain ⟨blocks,advances,hpack,hblocks,hadvances⟩ := packEight_exact bs xs blen xlen
  have material : eval oracle (modelMaterialize p (encodeState absorbed))=(log,ok (blocks,advances)) := by
    rw [modelMaterialize_eq_paired,state_roundtrip,heval packEight,hpack]
  have source : eval oracle
      (oracleProgram (PreparedQueryEffects.queries effects closedHashQueries D self 31#u8 payload))=
      ((address,absorbed)::log,
        finish (M := Result) closedHashQueries D {self with state:=encodeState absorbed} blocks advances) := by
    rw [query31_program_eq_model closedHashQueries p]
    unfold row31Model
    dsimp only [absorbed,address] at material
    simp only [eval,eval_bind,material,continueOracle,List.append_nil]
    rfl
  have model : eval oracle (fixedQuery31 self.state payload)=
      ((address,absorbed)::log,R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0 bs xs absorbed) := by
    unfold fixedQuery31
    dsimp only [absorbed,address] at heval
    simp only [eval,heval]
    rfl
  constructor
  · rw [source,model]
  · intro queries after success
    rw [source] at success
    obtain ⟨selected,hdecode,hafter⟩ := finish_accepted closedHashQueries D
      {self with state:=encodeState absorbed} after blocks advances queries success
    change Query31ConcreteMaterializedSchedule.actualConcreteDecode
      Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances=ok (.Ok (queries,selected)) at hdecode
    have decoded := Query31ConcreteMaterializedSchedule.adaptScanResult_success hdecode
    have scanned := AspisS1QueryScanModel.default_driver_scanOut blocks advances queries selected absorbed decoded
    rw [hblocks,hadvances] at scanned
    rw [model,hafter]
    exact ⟨scanned,rfl⟩

#print axioms modelMaterialize_eq_paired
#print axioms closed_query31_fixed_program
end AspisR1PublicPreparation.PreparedQueryMaterialize
