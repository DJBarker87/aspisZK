import GSConcreteRootRecoveryDefinitions

set_option autoImplicit false
namespace AspisR1.GSConcreteRootRecovery
open CompPoly Polynomial RRDenseCoeffVector
open AspisR1.RRConcreteState AspisR1.RRProgramRecoveryContracts
attribute [local irreducible] GSConcreteInterpolation.initial GSConcreteInterpolation.final

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

theorem initial_eq_recovery (q t : Nat) (points : Array (K × K))
    (hs : points.size = 1048576) (Q : CBivariate K)
    (hr : GSConcreteInterpolation.initial points = some Q)
    (H : {i : Nat // i ∈ Finset.range (1025 * 112)} → Fin t → K × K) :
    initial q t points hs H =
      (RRFixedTapeRecovery.recover 112 q t 1025 (GSConcreteInterpolation.initialState Q)
        (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.1
        (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.2 H).1 := by
  exact Option.pbind_some' (f := fun R hR =>
    (RRFixedTapeRecovery.recover 112 q t 1025 (GSConcreteInterpolation.initialState R)
      (GSConcreteInterpolation.initial_state_contract points hs R hR).2.1
      (GSConcreteInterpolation.initial_state_contract points hs R hR).2.2 H).1) hr

theorem final_eq_recovery (q t : Nat) (points : Array (K × K))
    (hs : points.size = 262144) (Q : CBivariate K)
    (hr : GSConcreteInterpolation.final points = some Q)
    (H : {i : Nat // i ∈ Finset.range (256 * 112)} → Fin t → K × K) :
    final q t points hs H =
      (RRFixedTapeRecovery.recover 112 q t 256 (GSConcreteInterpolation.finalState Q)
        (GSConcreteInterpolation.final_state_contract points hs Q hr).2.1
        (GSConcreteInterpolation.final_state_contract points hs Q hr).2.2 H).1 := by
  exact Option.pbind_some' (f := fun R hR =>
    (RRFixedTapeRecovery.recover 112 q t 256 (GSConcreteInterpolation.finalState R)
      (GSConcreteInterpolation.final_state_contract points hs R hR).2.1
      (GSConcreteInterpolation.final_state_contract points hs R hR).2.2 H).1) hr

#print axioms initial_eq_recovery
#print axioms final_eq_recovery
end AspisR1.GSConcreteRootRecovery
