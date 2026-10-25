import Tx2I_Witness
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2Q_Obstruction
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev K := OraclePortCheckpointAbiC5.K
abbrev E := OraclePortCheckpointAbiC5.E

/-- Symbolic recurrence fact; no concrete twelve-step reduction. -/
theorem zero_power (m : OraclePortCheckpointStateC3.Prepared K E)
    (s : QueryAccumulator.State K E) (h : s.power = 0) (n : Nat) :
    (OraclePortCheckpointStateC3.advance m n s).power = 0 ∧
    (OraclePortCheckpointStateC3.advance m n s).rhs = s.rhs := by
  induction n with
  | zero => exact ⟨h,rfl⟩
  | succ n ih =>
    simp only [OraclePortCheckpointStateC3.advance,QueryAccumulator.step,ih.1,
      zero_mul,map_zero,add_zero,ih.2,eq_self_iff_true,True.and_self]
    trivial

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
  · intro same
    have power := congrArg QueryAccumulator.State.power same
    have modelPower := QueryAccumulator.run_power
      LiteralOpeningView.eK (1 : K)
      (QueryAccumulator.extend22 (QueryResidualBridge.values data q))
      (QueryAccumulator.extend22 (QueryResidualBridge.basis (K := K) q)) 10
    change CheckpointBytes5Output.ofK (CheckpointBytes4ReaderFields.sourceK 0) = _ at power
    rw [CheckpointBytes5Output.ofK_source] at power
    change (QueryAccumulator.run _ _ _ _ _).power = _ at modelPower
    rw [one_pow] at modelPower
    exact zero_ne_one (power.trans modelPower)
  · intro same
    have rhs := congrArg QueryAccumulator.State.rhs same
    have retained := (zero_power
      (OraclePortCheckpointResumeC5.model data 1 q)
      (CheckpointBytes5Output.accumulator
        {a0 with
          rhs := CheckpointBytes4ReaderFields.sourceE 1,
          power := CheckpointBytes4ReaderFields.sourceK 0, next := 10#usize})
      (CheckpointBytes5Output.ofK_source 0) 12).2
    have bad := rhs.trans retained
    change CheckpointBytes5Output.ofE (CheckpointBytes4ReaderFields.sourceE 0) =
      CheckpointBytes5Output.ofE (CheckpointBytes4ReaderFields.sourceE 1) at bad
    rw [CheckpointBytes5Output.ofE_source,CheckpointBytes5Output.ofE_source] at bad
    exact zero_ne_one bad

#print axioms zero_power
#print axioms accepted_without_state_laws
end AspisR1.Tx2Q_Obstruction
end
