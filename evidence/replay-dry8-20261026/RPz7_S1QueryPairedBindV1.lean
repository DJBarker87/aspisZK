import RPz7_S1QueryFixedProgramV1
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result
open PreparedHashCode PreparedHashCode.QueryPair
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps AspisR1CurrentCaller.BorrowedClaimPrepared

theorem paired_bind_done {A B : Type} (out : List State → List State → A) (post : A → B)
    (n : Nat) (state : State) (blocks advances : List State) :
    AspisV8R19.OracleProgramOps.bind (pairedBytesProgram out n state blocks advances) (fun a => .done (post a))=
      pairedBytesProgram (fun bs xs => post (out bs xs)) n state blocks advances := by
  induction n generalizing state blocks advances with
  | zero => rfl
  | succ n ih => simp only [pairedBytesProgram,AspisV8R19.OracleProgramOps.bind,ih]

def sourceQueryLeaf {H : Type} (D : aspis_core.Digest32 H) (absorbed : transcript.Transcript H)
    (bs xs : List State) : Result (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H) := do
  let (blocks,advances) ← packEight bs xs
  finish (M := Result) closedHashQueries D absorbed blocks advances

/-- Full source query syntax equals the common seventeen-ask prefix followed
by its original pure scanner/embed/error continuation. This equality includes
ALL reply branches and every outer Result, not only successful executions. -/
theorem query31_program_paired {H M Cv : Type} {L : Nat} (p : FS2.Duplex.Params M Cv L)
    (D : aspis_core.Digest32 H) (self : transcript.Transcript H) (payload : Slice U8) :
    oracleProgram (PreparedQueryEffects.queries effects closedHashQueries D self 31#u8 payload)=
      .ask (flatten (CallerStep.openingAbsorbParts self.state 191#u8
        (UScalar.cast .U32 (Slice.len payload)) payload)) (fun absorbed =>
          pairedBytesProgram (sourceQueryLeaf D {self with state:=encodeState absorbed}) 8 absorbed [] []) := by
  rw [query31_program_eq_model closedHashQueries p]
  unfold row31Model
  congr 1
  funext absorbed
  rw [modelMaterialize_eq_paired,state_roundtrip]
  have continuation :
      (fun (r : Result (Blocks8 × Blocks8)) => continueOracle r fun pair => Program.done
        (finish (M := Result) closedHashQueries D {self with state:=encodeState absorbed} pair.1 pair.2))=
      (fun (r : Result (Blocks8 × Blocks8)) => Program.done (r >>= fun pair =>
        finish (M := Result) closedHashQueries D {self with state:=encodeState absorbed} pair.1 pair.2)) := by
    funext r
    cases r <;> rfl
  rw [continuation,paired_bind_done]
  rfl

#print axioms paired_bind_done
#print axioms query31_program_paired
end AspisR1PublicPreparation.PreparedQueryMaterialize
