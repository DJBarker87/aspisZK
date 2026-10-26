import FIn_ReducedHeadline
import FIn_ConcreteAccepted
import FIn_Nonvacuity
import FIn_QuarterAlias
import FIn_ViewTransport
import FIn_AcceptedRounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_FinalClosure
open AspisR1Stage2.Stage2Finish

/-- Final dictionary inventory. This is not a finish-law premise or a claim
that the retained pair slot has been linked to the shipped pair body. -/
theorem slots (seed : FinishOps FIn_WeightsInstall.W) :
    (FIn_WeightsInstall.install seed).field = FIn_Primitives.field ∧
    (FIn_WeightsInstall.install seed).add = FIn_Primitives.add ∧
    (FIn_WeightsInstall.install seed).polynomial = FIn_ExtractInstall.polynomial ∧
    (FIn_WeightsInstall.install seed).dot = SAG_DotClosed.source ∧
    (FIn_WeightsInstall.install seed).newWeights = FIn_WeightsInstall.newWeights ∧
    (FIn_WeightsInstall.install seed).pair = seed.pair :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms slots
#check @AspisR1.FIn_ReducedHeadline.deployed
#check @AspisR1.FIn_ConcreteAccepted.deployed
#check @AspisR1.FIn_Nonvacuity.witness_or_collision
end AspisR1.FIn_FinalClosure
end
