import RPz7_S1QueryAbsorbProgramV1
import RPz7_S1QueryFinishProgramV1
import RPz7_S1QueryByteChainBudgetV1
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps

def row31Model (B : QueriesModel.Boundaries) {H M Cv : Type} {L : Nat} (p : Params M Cv L)
    (D : aspis_core.Digest32 H) (self : transcript.Transcript H) (payload : Slice U8) :
    Program Bytes State (Result (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H)) :=
  .ask (flatten (CallerStep.openingAbsorbParts self.state 191#u8
    (UScalar.cast .U32 (Slice.len payload)) payload)) fun state =>
      AspisV8R19.OracleProgramOps.bind (modelMaterialize p (encodeState state))
        (fun r => continueOracle r fun pair =>
          .done (finish (M := Result) B D {self with state := encodeState state} pair.1 pair.2))

/-- The original query's complete program: exact source absorb, the fixed
mathematical paired sampler, and the original source scanner continuation. -/
theorem query31_program_eq_model (B : QueriesModel.Boundaries) {H M Cv : Type} {L : Nat}
    (p : Params M Cv L) (D : aspis_core.Digest32 H) (self : transcript.Transcript H) (payload : Slice U8) :
    oracleProgram (PreparedQueryEffects.queries effects B D self 31#u8 payload)=row31Model B p D self payload := by
  rw [queries_program_eq_model B p,query_absorb31_program]
  unfold row31Model
  simp only [AspisV8R19.OracleProgramOps.bind,continueOracle]
  congr 1
  funext state
  apply congrArg (fun next => AspisV8R19.OracleProgramOps.bind (modelMaterialize p (encodeState state)) next)
  funext result
  cases result with
  | fail e => rfl
  | div => rfl
  | ok pair =>
    cases pair
    simp only [continueOracle,finish_program]

/-- All outcomes, including scanner rejection/fail/div, have exactly seventeen
explicit byte-oracle reads. No per-attempt work credit or rejection conditioning. -/
theorem query31_reads (B : QueriesModel.Boundaries) {H M Cv : Type} {L : Nat}
    (p : Params M Cv L) (D : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (payload : Slice U8) (oracle : Bytes → State) :
    (eval oracle (oracleProgram (PreparedQueryEffects.queries effects B D self 31#u8 payload))).1.length=17 := by
  have empty (r : Result (Blocks8 × Blocks8)) (absorbed : transcript.Transcript H) :
      (eval oracle (continueOracle r fun pair =>
        Program.done (finish (M := Result) B D absorbed pair.1 pair.2))).1=[] := by
    cases r <;> rfl
  rw [query31_program_eq_model B p]
  unfold row31Model
  simp only [eval,eval_bind,List.length_cons,List.length_append,empty,
    modelMaterialize_reads,List.length_nil]

#print axioms query31_program_eq_model
#print axioms query31_reads
end AspisR1PublicPreparation.PreparedQueryMaterialize
