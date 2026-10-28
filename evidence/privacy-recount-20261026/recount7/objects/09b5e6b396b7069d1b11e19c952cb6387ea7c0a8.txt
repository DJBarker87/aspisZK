import R1Z.ProverRwP6PowersNativeCaller
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6PowersGammaSource
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6PowersNativeStep
variable [ExternalTypes]
-- Exact old/new source equation on arbitrary raw wide inputs. The old gamma
-- and kappa owners have already-proved algebraic value theorems.
theorem gamma (ops : ExternalFuns) (x : W) :
    (ProverRwP6PowersInstall.selected ops).op254 29#usize x =
      ProverRwP6ResultMap.map (ProverRwP6ArrayMap.map fromW)
        (AspisR1ProducerRelease47.gamma (toW x)) :=
  ProverRwP6PowersNativeCaller.exact_result ops 29#usize x 29#u8 (by decide)
theorem kappa (ops : ExternalFuns) (x : W) :
    (ProverRwP6PowersInstall.selected ops).op254 7#usize x =
      ProverRwP6ResultMap.map (ProverRwP6ArrayMap.map fromW)
        (AspisR1ProducerRelease47.kappa (toW x)) :=
  ProverRwP6PowersNativeCaller.exact_result ops 7#usize x 7#u8 (by decide)
#print axioms gamma
#print axioms kappa
end R1Z.ProverRwP6PowersGammaSource
