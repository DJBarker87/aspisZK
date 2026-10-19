import GSConcreteRootRecoveryDefinitions

set_option autoImplicit false
namespace AspisR1.GSConcreteRootRecovery
open CompPoly Polynomial RRDenseCoeffVector
open AspisR1.RRConcreteState AspisR1.RRProgramRecoveryContracts
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

theorem initial_eq_recovery (q t : Nat) (points : Array (K × K))
    (hs : points.size = 1048576) (Q : CBivariate K)
    (hr : GSConcreteInterpolation.initial points = some Q)
    (H : {i : Nat // i ∈ Finset.range (1025 * 112)} → Fin t → K × K) :
    initial q t points hs H =
      (RRFixedTapeRecovery.recover 112 q t 1025 (GSConcreteInterpolation.initialState Q)
        (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.1
        (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.2 H).1 := by
  unfold initial
  split
  next hnone =>
    exact False.elim (Option.noConfusion (hnone.symm.trans hr))
  next R hR =>
    have he : R = Q := Option.some.inj (hR.symm.trans hr)
    subst R
    rfl

theorem final_eq_recovery (q t : Nat) (points : Array (K × K))
    (hs : points.size = 262144) (Q : CBivariate K)
    (hr : GSConcreteInterpolation.final points = some Q)
    (H : {i : Nat // i ∈ Finset.range (256 * 112)} → Fin t → K × K) :
    final q t points hs H =
      (RRFixedTapeRecovery.recover 112 q t 256 (GSConcreteInterpolation.finalState Q)
        (GSConcreteInterpolation.final_state_contract points hs Q hr).2.1
        (GSConcreteInterpolation.final_state_contract points hs Q hr).2.2 H).1 := by
  unfold final
  split
  next hnone =>
    exact False.elim (Option.noConfusion (hnone.symm.trans hr))
  next R hR =>
    have he : R = Q := Option.some.inj (hR.symm.trans hr)
    subst R
    rfl

#print axioms initial_eq_recovery
#print axioms final_eq_recovery
end AspisR1.GSConcreteRootRecovery
