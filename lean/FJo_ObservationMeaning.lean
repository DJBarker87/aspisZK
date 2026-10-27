import FJo_QueryBatched
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_ObservationMeaning
open Aeneas Aeneas.Std Result AspisR1Stage2
attribute [local irreducible] TwoFoldExtraction.batchedWord
/-- Output of source success inversion, never an owner premise. -/
def Holds (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array FIp_DotsAdapter.E 29#usize) (geo : verifier.QueryGeometry)
    (data : MatchingSupport.Data AspisWideTower.WideExact) (query : Fin 262144) (j : Fin 22) : Prop :=
  ∃ a0 a1 b0 b1,a0.next.val=j.val ∧
    ∃ o : Port4C_QueryValues.Observation ops proof p a0 a1 g none geo b0 b1,
      Port5Q1_OpeningValues.values o.dots=FirstFold.fibre (TwoFoldExtraction.batchedWord data.W data.gamma) query
end AspisR1.FJo_ObservationMeaning
end
