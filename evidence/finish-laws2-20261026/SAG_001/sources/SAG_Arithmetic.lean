import SAF_ReducedLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_Arithmetic
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
variable {W : Type}

/-- Quarter meaning is independent of round bytes and polynomial. -/
theorem quarter_shared (ops : FinishOps W) (b0 b1 : Slice U8)
    (p0 p1 : Polynomial AspisWideTower.WideExact)
    (round1 : Port4D_Pairing.RoundLaws ops CheckpointBytes5Output.ofE b1 p1)
    (boundary : ∀ c0 c4 lhs, ops.field b0 0#usize = ok c0 →
      ops.field b0 4#usize = ok c4 → ops.add c0 c4 = ok lhs →
      CheckpointBytes5Output.ofE lhs = TwoRoundComparison.boundary p0)
    (evaluation : ∀ alpha value, ops.polynomial b0 alpha = ok value →
      CheckpointBytes5Output.ofE value = p0.eval (CheckpointBytes5Output.ofE alpha)) :
    Port4D_Pairing.RoundLaws ops CheckpointBytes5Output.ofE b0 p0 :=
  ⟨boundary, round1.quarter, evaluation⟩

/-- Six original law families, with the redundant first quarter family omitted. -/
structure Laws (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (d : MatchingSupport.Data AspisWideTower.WideExact) : Prop where
  boundary0 : ∀ c0 c4 lhs, ops.field v.round0 0#usize = ok c0 →
    ops.field v.round0 4#usize = ok c4 → ops.add c0 c4 = ok lhs →
    CheckpointBytes5Output.ofE lhs = TwoRoundComparison.boundary d.p0
  eval0 : ∀ alpha value, ops.polynomial v.round0 alpha = ok value →
    CheckpointBytes5Output.ofE value = d.p0.eval (CheckpointBytes5Output.ofE alpha)
  round1 : Port4D_Pairing.RoundLaws ops CheckpointBytes5Output.ofE v.round1 d.p1
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
    (d : MatchingSupport.Data AspisWideTower.WideExact) (laws : Laws ops v p d) :
    SAF_ReducedLaws.Arithmetic ops v p d :=
  ⟨quarter_shared ops v.round0 v.round1 d.p0 d.p1 laws.round1
    laws.boundary0 laws.eval0, laws.round1, laws.pair⟩

theorem forget (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (d : MatchingSupport.Data AspisWideTower.WideExact)
    (laws : SAF_ReducedLaws.Arithmetic ops v p d) : Laws ops v p d :=
  ⟨laws.round0.boundary, laws.round0.eval, laws.round1, laws.pair⟩

#print axioms quarter_shared
#print axioms reconstruct
#print axioms forget
end AspisR1.SAG_Arithmetic
end
