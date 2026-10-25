import Tx2I_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2I_Witness
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish

/-- Consistency fixture for the remaining explicit stage leaves, not their
production refinement. The authenticated shape and finish bodies stay installed. -/
def fixture (base : VTop_Stages.Ops) (x : E) (p0 : verifier.Prepared)
    (a0 : verifier.Accumulator) (geometry : verifier.QueryGeometry)
    (pending : verifier.BatchedWeights) : VTop_Stages.Ops :=
  {base with
    op0 := fun {T} {Err} o e => ok (match o with | some a => .Ok a | none => .Err e)
    op2 := fun _ => ok (some x)
    op5 := fun _ _ _ _ _ _ => ok (.Ok ())
    op6 := fun _ _ _ _ _ _ _ _ => ok (.Ok ({a0 with rhs := x, next := 22#usize},pending))
    op9 := fun _ s => ok s
    op10 := fun _ => ok (.Ok pending)
    op11 := fun _ _ _ => ok (.Ok geometry)
    op13 := fun _ _ => ok ()
    op14 := ok 32#usize
    op15 := ok 0#usize
    op16 := ok 10#usize
    op17 := fun n _ => ok (Array.repeat n x)
    op18 := fun _ _ _ _ _ _ => ok (.Ok
      ({p0 with variant := .S2, alpha := Array.repeat 2#usize x}, {a0 with next := 10#usize}))
    op20 := ok 32#usize
    op21 := ok 32#usize
    op22 := ok 0#usize
    op23 := ok 0#usize
    unwrap32 := fun r => match r with | .Ok a => ok a | .Err _ => .div}

theorem authenticated_success (base : VTop_Stages.Ops) (x : E) (p0 : verifier.Prepared)
    (a0 : verifier.Accumulator) (geometry : verifier.QueryGeometry)
    (pending : verifier.BatchedWeights) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub checkpoint : Slice U8) :
    VTop_Stages.verifier.candidate.tx2_authenticated
      (Tx2I_Install.stage (fixture base x p0 a0 geometry pending) (Tx2I_Nonvacuity.leaves x))
      D pub Op3I_Witness.proof checkpoint hash none = ok (.Ok ()) := by
  have len : Op3I_Witness.proof.length = 57607 := Op3I_Witness.fields.1
  have bound : 32#usize ≤ Op3I_Witness.proof.length := by scalar_tac
  simp only [VTop_Stages.verifier.candidate.tx2_authenticated,Tx2I_Install.stage,
    Tx2I_Nonvacuity.shape_success,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,fixture,
    VTop_Stages.verifier.candidate.tx2_common, bne_self_eq_false, Bool.false_eq_true,
    if_false,core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice.index,
    show 0#usize ≤ 0#usize ∧ 0#usize ≤ Op3I_Witness.proof.length by scalar_tac,
    show 0#usize ≤ 32#usize ∧ 32#usize ≤ Op3I_Witness.proof.length by scalar_tac,
    show 32#usize ≤ 32#usize ∧ 32#usize ≤ Op3I_Witness.proof.length by scalar_tac,
    if_true,core.array.TryFromArrayCopySlice.try_from]
  simp only [Slice.length,List.length_take,List.length_drop,List.slice,len]
  simp only [show min (32#usize).val (57607-(0#usize).val) = (32#usize).val by decide,
    beq_self_eq_true,if_true,bind_tc_ok]
  apply Tx2I_Nonvacuity.finish_success

#print axioms authenticated_success
end AspisR1.Tx2I_Witness
end
