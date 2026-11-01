import R1Z.PV_RunJoin_NativeResidual63
import R1Z.PV_RunJoin_WeightMap46
import R1Z.ProverCommitWideOps48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativePowerCarrier66
open Aeneas Aeneas.Std Result ProverRwFull
abbrev W := PV_B1_254.aspis_core.field.wide_exact.WideExact
abbrev S := ProverCommitWideOps48.Source
def toS (x : W) : S := ProverRwDictionaryTower.toW (PV_B1_ActualCarrierWide.fromW x)
theorem mul (x y : W) :
    PV_RunJoin_WeightMap46.mapResult toS (PV_B1_254.aspis_core.field.wide_exact.WideExact.mul x y)=
      AspisR1ProducerRelease47.field.wide_exact.WideExact.mul (toS x) (toS y) := by
  rfl
#print axioms toS
#print axioms mul
end R1Z.PV_RunJoin_NativePowerCarrier66
