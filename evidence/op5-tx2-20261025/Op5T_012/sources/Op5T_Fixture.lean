import Op5T_Marks
import MultiproofConeSlices
set_option autoImplicit false
noncomputable section
namespace AspisR1.Op5T_Fixture
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish

/-- Remaining-leaf consistency fixture. Shape remains the installed source;
this is not a production batch certificate or an accepted SDK spend. -/
def fixture (base : VTop_Stages.Ops) (x : E) (p : verifier.Prepared)
    (a : verifier.Accumulator) (geometry : verifier.QueryGeometry)
    (pending : verifier.BatchedWeights) (saved : alloc.vec.Vec U8) : VTop_Stages.Ops :=
  {Tx2I_Witness.fixture base x p a geometry pending with
    op1 := ok x
    op4 := fun _ => ok (.Ok ())
    op7 := fun _ _ _ _ _ g => ok (.Ok p,g)
    op8 := fun _ _ _ _ _ _ => ok saved
    op12 := fun _ => ok (.Ok a)}

theorem success (base : VTop_Stages.Ops) (x : E) (p : verifier.Prepared)
    (a : verifier.Accumulator) (geometry : verifier.QueryGeometry)
    (pending : verifier.BatchedWeights) (saved : alloc.vec.Vec U8) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub : Slice U8) :
    VTop_Stages.verifier.candidate.tx1
      (Tx2I_Install.stage (fixture base x p a geometry pending saved) (Tx2I_Nonvacuity.leaves x))
      D semantic pub Op3I_Witness.proof 10#usize hash none = ok (.Ok saved) := by
  have bound : (32#usize).val ≤ Op3I_Witness.proof.val.length := by
    rw [Op3I_Witness.fields.1]
    decide
  have range := MultiproofConeSlices.range_total Op3I_Witness.proof 0#usize 32#usize (by decide) bound
  have len := MultiproofConeSlices.sub_length Op3I_Witness.proof 0#usize 32#usize (by decide) bound
  have viewLen : (MultiproofConeSlices.sub Op3I_Witness.proof 0#usize 32#usize).length = (32#usize).val := len
  have convert : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
      (MultiproofConeSlices.sub Op3I_Witness.proof 0#usize 32#usize) =
      ok (.Ok ⟨(MultiproofConeSlices.sub Op3I_Witness.proof 0#usize 32#usize).val, len⟩) := by
    simp only [core.array.TryFromArrayCopySlice.try_from,viewLen, dite_true]
  simp only [VTop_Stages.verifier.candidate.tx1,Tx2I_Install.stage,
    Tx2I_Nonvacuity.shape_success,fixture,Tx2I_Witness.fixture,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.Insts.CoreOpsTry.branch,bne_self_eq_false,Bool.false_eq_true,
    if_false,range,convert]

/-- The successful fixture satisfies the accepted-source marking statement,
using the body's own typed trace. No successful source call is an input. -/
theorem nonvacuity (base : VTop_Stages.Ops) (x : E) (p : verifier.Prepared)
    (a : verifier.Accumulator) (geometry : verifier.QueryGeometry)
    (pending : verifier.BatchedWeights) (saved : alloc.vec.Vec U8) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub : Slice U8) :
    ∃ log, VTop_Trace.run
      (Tx2I_Install.stage (fixture base x p a geometry pending saved) (Tx2I_Nonvacuity.leaves x))
      (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub Op3I_Witness.proof 10#usize hash none) [] =
      ok (.Ok saved,log) ∧ Op5C_RejectedMarks.sourceSites log = [.batch0,.query0,.save] :=
  Op5T_Marks.accepted_source_marks _ D hash semantic pub _ _ none saved
    (success base x p a geometry pending saved D hash semantic pub)

#print axioms success
#print axioms nonvacuity
end AspisR1.Op5T_Fixture
end
