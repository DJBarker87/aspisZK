import Tx2I_Witness
import Tx2Q_StateObstruction
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2Q_Obstruction
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev K := OraclePortCheckpointAbiC5.K
abbrev E := OraclePortCheckpointAbiC5.E
attribute [local irreducible] OraclePortCheckpointStateC3.advance
  OraclePortCheckpointStateC3.write QueryAccumulator.run

/-- This is an interface countermodel, NOT a production operation instance.
The actual extracted authenticated TX2 control, concrete shape, and installed
finish are executed on the existing symbolic 57607-byte fixture. Its free
op18/op6/op9 slots return these exact states, so acceptance alone cannot imply
the two state equations on the actual exported arguments. -/
theorem accepted_without_state_laws
    (base : VTop_Stages.Ops) (p0 : verifier.Prepared) (a0 : verifier.Accumulator)
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub checkpoint : Slice U8) (data : MatchingSupport.Data E)
    (q : Fin 22 → Fin 262144) :
    let x := CheckpointBytes4ReaderFields.sourceE 0
    let initState := {a0 with
      rhs := CheckpointBytes4ReaderFields.sourceE 1,
      power := CheckpointBytes4ReaderFields.sourceK 0}
    let ops := Tx2I_Witness.fixture base x p0 initState geometry pending
    let saved := {initState with next := 10#usize}
    let returned := {initState with rhs := x, next := 22#usize}
    let m := OraclePortCheckpointResumeC5.model data 1 q
    VTop_Stages.verifier.candidate.tx2_authenticated
      (Tx2I_Install.stage ops (Tx2I_Nonvacuity.leaves x))
      D pub Op3I_Witness.proof checkpoint hash none = ok (.Ok ()) ∧
    ops.op18 D checkpoint Op3I_Witness.proof pub .S2 hash =
      ok (.Ok ({p0 with variant := .S2, alpha := Array.repeat 2#usize x},saved)) ∧
    (∀ g, ops.op6 Op3I_Witness.proof
      {p0 with variant := .S2, alpha := Array.repeat 2#usize x}
      saved g none geometry pending 22#usize = ok (.Ok (returned,pending))) ∧
    ops.op9 pending returned.weights.deref = ok returned.weights.deref ∧
    CheckpointBytes5Output.accumulator saved ≠
      (OraclePortCheckpointStateC3.write m).accumulator ∧
    CheckpointBytes5Output.accumulator returned ≠
      OraclePortCheckpointStateC3.advance m 12
        (CheckpointBytes5Output.accumulator saved) := by
  dsimp only
  refine ⟨Tx2I_Witness.authenticated_success base _ p0 _ geometry pending D hash pub checkpoint,
    rfl,fun _ => rfl,rfl,?_,?_⟩
  · apply Tx2Q_StateObstruction.not_saved
    exact CheckpointBytes5Output.ofK_source 0
  · apply Tx2Q_StateObstruction.not_twelve
    · exact CheckpointBytes5Output.ofK_source 0
    · change CheckpointBytes5Output.ofE (CheckpointBytes4ReaderFields.sourceE 0) ≠
        CheckpointBytes5Output.ofE (CheckpointBytes4ReaderFields.sourceE 1)
      rw [CheckpointBytes5Output.ofE_source,CheckpointBytes5Output.ofE_source]
      exact zero_ne_one

#print axioms accepted_without_state_laws
end AspisR1.Tx2Q_Obstruction
end
