import S1QueryContinuationTotalV1
import S1QueryDecodeTotalV1
import S1QueryFixedProgramV1
set_option autoImplicit false
noncomputable section
namespace AspisS1QueryProgramTotal
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedQueryMaterialize
open AspisR1PublicPreparation.PreparedHashCode AspisR1PublicPreparation.PreparedHashCode.QueryPair
open AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- TOTAL source byte-oracle interpretation of the actual complete row31
query call, including all rejection continuations, 22 embeddings and trace
operations. Native allocation/abort and SDK/runtime are separate boundaries. -/
theorem row31_total {H M Cv : Type} {L : Nat} (p : Params M Cv L)
    (D : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (payload : Slice U8) (oracle : Bytes → State) :
    ∃ result : core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H,
      (eval oracle (oracleProgram (PreparedQueryEffects.queries effects closedHashQueries
        D self 31#u8 payload))).2=ok result := by
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
  obtain ⟨sf,selected,called,valid⟩ := AspisS1QueryDecodeTotal.closed_decode_total blocks advances
  have total := AspisS1QueryContinuationTotal.finish_of_decoded D
    {self with state:=encodeState absorbed} blocks advances _ called
  refine ⟨_,?_⟩
  rw [source]
  exact total

#print axioms row31_total
end AspisS1QueryProgramTotal
