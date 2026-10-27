import SAG_QuarterFree
set_option autoImplicit false
noncomputable section
attribute [local irreducible] QuadraticAlgebra.instInv
namespace AspisR1.FIn_QuarterAlias
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish

/-- Each actual RoundLaws.quarter projection has exactly this SAME predicate,
independent of the round's byte slice and model polynomial. -/
theorem field_type {W : Type} (ops : FinishOps W) (bytes : Slice U8)
    (poly : Polynomial AspisWideTower.WideExact)
    (law : Port4D_Pairing.RoundLaws ops CheckpointBytes5Output.ofE bytes poly) :
    SAG_QuarterFree.QuarterMeaning ops := law.quarter

theorem same_predicate {W : Type} (ops : FinishOps W) (b0 b1 : Slice U8)
    (p0 p1 : Polynomial AspisWideTower.WideExact)
    (r0 : Port4D_Pairing.RoundLaws ops CheckpointBytes5Output.ofE b0 p0)
    (r1 : Port4D_Pairing.RoundLaws ops CheckpointBytes5Output.ofE b1 p1) :
    field_type ops b0 p0 r0=field_type ops b1 p1 r1 := Subsingleton.elim _ _

#print axioms field_type
#print axioms same_predicate
#print AspisR1.Port4D_Pairing.RoundLaws
#print AspisR1.SAG_QuarterFree.QuarterMeaning
end AspisR1.FIn_QuarterAlias
end
