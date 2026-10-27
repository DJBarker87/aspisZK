import R1Z.ProverRwP6PowersGammaSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6PowersGammaValues
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6PowersNativeStep
open ProverCommitWideOps48
variable [ExternalTypes]
def fieldArray (N : Usize) (ys : Nat → Raw) : Array W N :=
  ProverRwP6ArrayMap.map fromW (ProverCommitMix48.sourceArray N ys)

theorem gamma (ops : ExternalFuns) (x : Raw) (hx : canonical x) :
    ∃ ys : Nat → Raw,
      (ProverRwP6PowersInstall.selected ops).op254 29#usize (fromW (source x)) = ok (fieldArray 29#usize ys) ∧
      (∀ k, k<29 → canonical (ys k)) ∧ ∀ k, k<29 → value (ys k)=value x^k := by
  obtain ⟨ys,hy,hc,hv⟩ := ProverCommitGamma48.gamma_exact x hx
  refine ⟨ys,?_,hc,hv⟩
  have native : AspisR1ProducerRelease47.gamma (toW (fromW (source x))) =
      ok (ProverCommitMix48.sourceArray 29#usize ys) :=
    (congrArg AspisR1ProducerRelease47.gamma
      (ProverRwDictionaryTower.native_w_roundtrip (source x))).trans hy
  exact (ProverRwP6PowersGammaSource.gamma ops (fromW (source x))).trans
    (congrArg (ProverRwP6ResultMap.map (ProverRwP6ArrayMap.map fromW)) native)

theorem kappa (ops : ExternalFuns) (x : Raw) (hx : canonical x) :
    ∃ ys : Nat → Raw,
      (ProverRwP6PowersInstall.selected ops).op254 7#usize (fromW (source x)) = ok (fieldArray 7#usize ys) ∧
      (∀ k, k<7 → canonical (ys k)) ∧ ∀ k, k<7 → value (ys k)=value x^k := by
  obtain ⟨ys,hy,hc,hv⟩ := ProverCommitGamma48.kappa_exact x hx
  refine ⟨ys,?_,hc,hv⟩
  have native : AspisR1ProducerRelease47.kappa (toW (fromW (source x))) =
      ok (ProverCommitMix48.sourceArray 7#usize ys) :=
    (congrArg AspisR1ProducerRelease47.kappa
      (ProverRwDictionaryTower.native_w_roundtrip (source x))).trans hy
  exact (ProverRwP6PowersGammaSource.kappa ops (fromW (source x))).trans
    (congrArg (ProverRwP6ResultMap.map (ProverRwP6ArrayMap.map fromW)) native)
#print axioms gamma
#print axioms kappa
end R1Z.ProverRwP6PowersGammaValues
