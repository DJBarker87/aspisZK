import R1Z.ProverCommitSemanticSource28
import R1Z.ProverCommitLogged28
/-! Real host_semantic scalar-emission boundary. Records are supplied at this
boundary; this module does not assert that real message production equals the
model. The native control/append binding is checked separately by Kani. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.RealR3_SemanticEmission
open Aeneas Aeneas.Std Result ProverCommitStateLift28
open AspisR1SimSemantic20
abbrev Bytes := alloc.vec.Vec U8
abbrev Q := aspis_core.field.QM31
abbrev Error := r1_wire.Error
abbrev State := r1_wire.SemanticTranscript Unit
abbrev ScalarResult := core.result.Result Q Error
abbrev RowsResult := core.result.Result Unit Error

/-- The framed record is appended only after a successful challenge. The
returned transcript and complete oracle machine survive semantic rejection. -/
def emit {S : Type} (effect : Unit → Parts → Port S Bytes32)
    (state : State) (row : U8) (framed : Bytes) (outputPrefix : List U8) :
    Port S (ScalarResult × State × List U8) := do
  let (value,next) ← ProverCommitSemanticProgram28.semantic effect state row framed
  match value with
  | .Err e => pure (.Err e,next,outputPrefix)
  | .Ok q => pure (.Ok q,next,outputPrefix ++ framed.val)

theorem success {S : Type} (effect : Unit → Parts → Port S Bytes32)
    (state next : State) (row : U8) (framed : Bytes) (outputPrefix : List U8)
    (machine after : S) (q : Q)
    (called : ProverCommitSemanticProgram28.semantic effect state row framed machine =
      ok ((.Ok q,next),after)) :
    emit effect state row framed outputPrefix machine =
      ok ((.Ok q,next,outputPrefix ++ framed.val),after) := by
  simp only [emit,bind_run,called,bind_tc_ok]
  rfl

theorem rejected {S : Type} (effect : Unit → Parts → Port S Bytes32)
    (state next : State) (row : U8) (framed : Bytes) (outputPrefix : List U8)
    (machine after : S) (e : Error)
    (called : ProverCommitSemanticProgram28.semantic effect state row framed machine =
      ok ((.Err e,next),after)) :
    emit effect state row framed outputPrefix machine = ok ((.Err e,next,outputPrefix),after) := by
  simp only [emit,bind_run,called,bind_tc_ok]
  rfl

/-- Mathematical CoinOracle instantiation of the emission owner. The real
caller uses LegacyHashFn, not CoinOracle: this is not its native hash binding.
The ordered call/answer history is retained in this model instantiation. -/
theorem ordered_effects (state : State) (row : U8) (framed : Bytes)
    (outputPrefix : List U8) (machine : ProverCommitLogged28.LoggedMachine) :
    emit (ProverCommitLogged28.dictionary ProverCommitControl28.extracted)
      state row framed outputPrefix machine =
    emit (ProverCommitLogged28.dictionary ProverCommitControl28.reference)
      state row framed outputPrefix machine := by
  exact install _ _ (ProverCommitLogged28.logged_exact _ _ ProverCommitCoinCall27.call_exact)
    (fun e => emit (fun (_ : Unit) p => read e p) state row framed outputPrefix) machine

/-- A recursive real emission owner consumes an ordered frame list. A failed
row stops immediately; no suffix is queried or appended. -/
def rows {S : Type} (effect : Unit → Parts → Port S Bytes32) :
    List (U8 × Bytes) → State → List U8 → Port S (RowsResult × State × List U8)
  | [],state,outputPrefix => pure (.Ok (),state,outputPrefix)
  | (row,framed)::tail,state,outputPrefix => do
    let (value,next,bytes) ← emit effect state row framed outputPrefix
    match value with
    | .Err e => pure (.Err e,next,bytes)
    | .Ok _ => rows effect tail next bytes

/-- The mathematical CoinOracle interpreter is installed through every row.
This does not identify LegacyHashFn with that machine or establish RunJoin. -/
theorem rows_ordered_effects (frames : List (U8 × Bytes)) (state : State)
    (outputPrefix : List U8) (machine : ProverCommitLogged28.LoggedMachine) :
    rows (ProverCommitLogged28.dictionary ProverCommitControl28.extracted)
      frames state outputPrefix machine =
    rows (ProverCommitLogged28.dictionary ProverCommitControl28.reference)
      frames state outputPrefix machine := by
  exact install _ _ (ProverCommitLogged28.logged_exact _ _ ProverCommitCoinCall27.call_exact)
    (fun e => rows (fun (_ : Unit) p => read e p) frames state outputPrefix) machine

#print axioms success
#print axioms rejected
#print axioms ordered_effects
#print axioms rows_ordered_effects
end R1Z.RealR3_SemanticEmission
