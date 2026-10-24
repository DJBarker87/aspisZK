import S1QueryMaterializeModelV1
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def queriesWithPairs (B : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    Code (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H) := do
  let absorbed ← PreparedHashEffects.absorb effects D self row payload
  let (blocks,advances) ← materializePairs D absorbed.hash absorbed.state
  finish B D absorbed blocks advances

/-- Complete source Code equality, including rejection/error continuations. -/
theorem queries_code_eq_pairs (B : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    PreparedQueryEffects.queries effects B D self row payload=queriesWithPairs B D self row payload := by
  rw [code_eq_factored]
  unfold queriesFactored queriesWithPairs
  congr 1
  funext absorbed
  rw [materialize_code_eq_pairs]

/-- Actual full source query: source absorb followed by the FIXED mathematical
chain, then the SAME decoder/embedding/error continuation on its returned arrays.
No separate materializer, scanner or embedding success premise is supplied. -/
theorem queries_program_eq_model (B : QueriesModel.Boundaries) {H M Cv : Type} {L : Nat}
    (p : Params M Cv L) (D : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    oracleProgram (PreparedQueryEffects.queries effects B D self row payload)=
      AspisV8R19.OracleProgramOps.bind
        (oracleProgram (PreparedHashEffects.absorb effects D self row payload))
        (fun r => continueOracle r fun absorbed =>
          AspisV8R19.OracleProgramOps.bind (modelMaterialize p absorbed.state)
            (fun r => continueOracle r fun pair => oracleProgram (finish B D absorbed pair.1 pair.2))) := by
  rw [code_eq_factored]
  unfold queriesFactored
  rw [oracleProgram_bind]
  congr 1
  funext r
  cases r with
  | fail e => rfl
  | div => rfl
  | ok absorbed =>
    change oracleProgram (do let pair ← materialize effects D absorbed.hash absorbed.state
                            finish B D absorbed pair.1 pair.2)=_
    rw [oracleProgram_bind,materialize_eq_model p]
    rfl

/-- TOTAL in the source byte-oracle interpretation: all fixed array operations
succeed for every oracle. This is not a native allocation/abort theorem. -/
theorem materialize_program_total {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (state : Bytes32) (oracle : Bytes → State) :
    ∃ arrays, (eval oracle (oracleProgram (materialize effects D hash state))).2=ok arrays := by
  rw [materialize_program]
  unfold normalMaterialize
  simp only [eval]
  exact ⟨_,rfl⟩

#print axioms queries_code_eq_pairs
#print axioms queries_program_eq_model
#print axioms materialize_program_total
end AspisR1PublicPreparation.PreparedQueryMaterialize
