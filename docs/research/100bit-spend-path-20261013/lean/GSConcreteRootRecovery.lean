import GSConcreteRootRecoveryEquations
import GSRootCandidateContract

set_option autoImplicit false
namespace AspisR1.GSConcreteRootRecovery
open CompPoly Polynomial RRDenseCoeffVector
open AspisR1.RRConcreteState AspisR1.RRProgramRecoveryContracts
open AspisR1.CompPolyFactorMeanTools
open AspisV8R19.OracleResampling AspisV8PairedCommitment
attribute [local irreducible] GSConcreteInterpolation.initial GSConcreteInterpolation.final
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

abbrev Candidates (Q : CBivariate K) (d : Nat) (cs : List (List K)) : Prop :=
  AspisWide.GSRootCandidateContract.Candidates (CBivariate.toPoly Q) d cs

theorem initial_correct [Fintype K] (q t : Nat) (points : Array (K × K))
    (hs : points.size = 1048576) (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range (1025 * 112)} → Fin t → K × K)
    (cs : List (List K)) (hout : initial q t points hs H = some cs) :
    ∃ Q, GSConcreteInterpolation.initial points = some Q ∧ Candidates Q 1025 cs := by
  obtain ⟨Q, hr, hw⟩ := GSConcreteInterpolation.initial_exists points hs
  have hc := GSConcreteInterpolation.initial_state_contract points hs Q hr
  have hres : (RRFixedTapeRecovery.recover 112 q t 1025
      (GSConcreteInterpolation.initialState Q) hc.2.1 hc.2.2 H).1 = some cs := by
    rw [← initial_eq_recovery q t points hs Q hr H]
    exact hout
  have hcan := RRFixedTapeRecovery.recover_correct 112 q t 1025
    (GSConcreteInterpolation.initialState Q) hc.2.1 hc.2.2 hq H cs hres
  refine ⟨Q, hr, ?_⟩
  constructor
  · intro candidate hmem
    have he := congrArg (fun R : (K[X])[X] => R.eval (toPolynomial candidate)) hc.1
    exact he.symm.trans (hcan.1 candidate hmem)
  · intro f hf hbound
    have he := congrArg (fun R : (K[X])[X] => R.eval f) hc.1
    exact hcan.2 f (he.trans hf) hbound

theorem final_correct [Fintype K] (q t : Nat) (points : Array (K × K))
    (hs : points.size = 262144) (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range (256 * 112)} → Fin t → K × K)
    (cs : List (List K)) (hout : final q t points hs H = some cs) :
    ∃ Q, GSConcreteInterpolation.final points = some Q ∧ Candidates Q 256 cs := by
  obtain ⟨Q, hr, hw⟩ := GSConcreteInterpolation.final_exists points hs
  have hc := GSConcreteInterpolation.final_state_contract points hs Q hr
  have hres : (RRFixedTapeRecovery.recover 112 q t 256
      (GSConcreteInterpolation.finalState Q) hc.2.1 hc.2.2 H).1 = some cs := by
    rw [← final_eq_recovery q t points hs Q hr H]
    exact hout
  have hcan := RRFixedTapeRecovery.recover_correct 112 q t 256
    (GSConcreteInterpolation.finalState Q) hc.2.1 hc.2.2 hq H cs hres
  refine ⟨Q, hr, ?_⟩
  constructor
  · intro candidate hmem
    have he := congrArg (fun R : (K[X])[X] => R.eval (toPolynomial candidate)) hc.1
    exact he.symm.trans (hcan.1 candidate hmem)
  · intro f hf hbound
    have he := congrArg (fun R : (K[X])[X] => R.eval f) hc.1
    exact hcan.2 f (he.trans hf) hbound

noncomputable section
variable [Fintype K]

theorem initial_abort_le (q t : Nat) (points : Array (K × K))
    (hs : points.size = 1048576) (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    mean (fun H : {i : Nat // i ∈ Finset.range (1025 * 112)} → Fin t → K × K =>
      abortIndicator (initial q t points hs H)) ≤ (1025 : ℚ) * 112 * (1/2)^t := by
  obtain ⟨Q, hr, hw⟩ := GSConcreteInterpolation.initial_exists points hs
  have hc := GSConcreteInterpolation.initial_state_contract points hs Q hr
  have hm := RRFixedTapeRecovery.recover_abort_le 112 q t 1025
    (GSConcreteInterpolation.initialState Q) hc.2.1 hc.2.2 hq hodd
  have he : (fun H : {i : Nat // i ∈ Finset.range (1025 * 112)} → Fin t → K × K =>
      abortIndicator (initial q t points hs H)) =
      (fun H => abortIndicator (RRFixedTapeRecovery.recover 112 q t 1025
        (GSConcreteInterpolation.initialState Q) hc.2.1 hc.2.2 H).1) := by
    funext H
    exact congrArg abortIndicator (initial_eq_recovery q t points hs Q hr H)
  rw [he]
  exact hm

theorem final_abort_le (q t : Nat) (points : Array (K × K))
    (hs : points.size = 262144) (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    mean (fun H : {i : Nat // i ∈ Finset.range (256 * 112)} → Fin t → K × K =>
      abortIndicator (final q t points hs H)) ≤ (256 : ℚ) * 112 * (1/2)^t := by
  obtain ⟨Q, hr, hw⟩ := GSConcreteInterpolation.final_exists points hs
  have hc := GSConcreteInterpolation.final_state_contract points hs Q hr
  have hm := RRFixedTapeRecovery.recover_abort_le 112 q t 256
    (GSConcreteInterpolation.finalState Q) hc.2.1 hc.2.2 hq hodd
  have he : (fun H : {i : Nat // i ∈ Finset.range (256 * 112)} → Fin t → K × K =>
      abortIndicator (final q t points hs H)) =
      (fun H => abortIndicator (RRFixedTapeRecovery.recover 112 q t 256
        (GSConcreteInterpolation.finalState Q) hc.2.1 hc.2.2 H).1) := by
    funext H
    exact congrArg abortIndicator (final_eq_recovery q t points hs Q hr H)
  rw [he]
  exact hm

#print axioms initial_correct
#print axioms final_correct
#print axioms initial_abort_le
#print axioms final_abort_le
end
end AspisR1.GSConcreteRootRecovery
