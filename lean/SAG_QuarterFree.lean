import SAG_Arithmetic
set_option autoImplicit false
noncomputable section
attribute [local irreducible] QuadraticAlgebra.instInv
namespace AspisR1.SAG_QuarterFree
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
variable {W : Type}

abbrev QuarterMeaning (ops : FinishOps W) : Prop :=
  ∀ m claim rhs, ops.quarter = ok m → ops.mulM claim m = ok rhs →
    CheckpointBytes5Output.ofE rhs = RoundPairing.quarter * CheckpointBytes5Output.ofE claim

/-- Five remaining arithmetic families; both quarter meanings are outputs of
the explicitly installed native scalar body. -/
structure Arithmetic (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (d : MatchingSupport.Data AspisWideTower.WideExact) : Prop where
  boundary0 : ∀ c0 c4 lhs, ops.field v.round0 0#usize = ok c0 →
    ops.field v.round0 4#usize = ok c4 → ops.add c0 c4 = ok lhs →
    CheckpointBytes5Output.ofE lhs = TwoRoundComparison.boundary d.p0
  eval0 : ∀ alpha value, ops.polynomial v.round0 alpha = ok value →
    CheckpointBytes5Output.ofE value = d.p0.eval (CheckpointBytes5Output.ofE alpha)
  boundary1 : ∀ c0 c4 lhs, ops.field v.round1 0#usize = ok c0 →
    ops.field v.round1 4#usize = ok c4 → ops.add c0 c4 = ok lhs →
    CheckpointBytes5Output.ofE lhs = TwoRoundComparison.boundary d.p1
  eval1 : ∀ alpha value, ops.polynomial v.round1 alpha = ok value →
    CheckpointBytes5Output.ofE value = d.p1.eval (CheckpointBytes5Output.ofE alpha)
  pair : ∀ (weights : W) (alphas : Slice E) (value : E),
    ops.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights) →
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha { «end» := 2#usize } = ok alphas →
    ops.pair weights alphas v.final_message p.kappa = ok (.Ok value) →
    CheckpointBytes5Output.ofE value = RoundPairing.dot d.f
      (RoundPairing.dualFold (n := 64) d.alpha1
        (RoundPairing.dualFold (n := 256) d.alpha0
          (FunctionalWeights.weights d.F d.F0 d.kappa)))

theorem reconstruct (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (d : MatchingSupport.Data AspisWideTower.WideExact)
    (quarter : QuarterMeaning ops) (laws : Arithmetic ops v p d) :
    SAF_ReducedLaws.Arithmetic ops v p d :=
  ⟨⟨laws.boundary0,quarter,laws.eval0⟩,⟨laws.boundary1,quarter,laws.eval1⟩,laws.pair⟩

#print axioms reconstruct
end AspisR1.SAG_QuarterFree
end
