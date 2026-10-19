import GSConcreteInterpolation
import RRFixedTapeRecovery

set_option autoImplicit false
namespace AspisR1.GSConcreteRootRecovery
open CompPoly Polynomial RRDenseCoeffVector
open AspisR1.RRConcreteState AspisR1.RRProgramRecoveryContracts
open AspisR1.CompPolyFactorMeanTools
open AspisV8R19.OracleResampling AspisV8PairedCommitment

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

def initial (q t : Nat) (points : Array (K × K)) (hs : points.size = 1048576)
    (H : {i : Nat // i ∈ Finset.range (1025 * 112)} → Fin t → K × K) :
    Option (List (List K)) :=
  match hr : GSConcreteInterpolation.initial points with
  | none => none
  | some Q =>
    let hc := GSConcreteInterpolation.initial_state_contract points hs Q hr
    (RRFixedTapeRecovery.recover 112 q t 1025 (GSConcreteInterpolation.initialState Q)
      hc.2.1 hc.2.2 H).1

def final (q t : Nat) (points : Array (K × K)) (hs : points.size = 262144)
    (H : {i : Nat // i ∈ Finset.range (256 * 112)} → Fin t → K × K) :
    Option (List (List K)) :=
  match hr : GSConcreteInterpolation.final points with
  | none => none
  | some Q =>
    let hc := GSConcreteInterpolation.final_state_contract points hs Q hr
    (RRFixedTapeRecovery.recover 112 q t 256 (GSConcreteInterpolation.finalState Q)
      hc.2.1 hc.2.2 H).1

theorem initial_eq_recovery (q t : Nat) (points : Array (K × K))
    (hs : points.size = 1048576) (Q : CBivariate K)
    (hr : GSConcreteInterpolation.initial points = some Q)
    (H : {i : Nat // i ∈ Finset.range (1025 * 112)} → Fin t → K × K) :
    initial q t points hs H =
      (RRFixedTapeRecovery.recover 112 q t 1025 (GSConcreteInterpolation.initialState Q)
        (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.1
        (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.2 H).1 := by
  simp only [initial, hr]

theorem final_eq_recovery (q t : Nat) (points : Array (K × K))
    (hs : points.size = 262144) (Q : CBivariate K)
    (hr : GSConcreteInterpolation.final points = some Q)
    (H : {i : Nat // i ∈ Finset.range (256 * 112)} → Fin t → K × K) :
    final q t points hs H =
      (RRFixedTapeRecovery.recover 112 q t 256 (GSConcreteInterpolation.finalState Q)
        (GSConcreteInterpolation.final_state_contract points hs Q hr).2.1
        (GSConcreteInterpolation.final_state_contract points hs Q hr).2.2 H).1 := by
  simp only [final, hr]

def Candidates (Q : CBivariate K) (d : Nat) (cs : List (List K)) : Prop :=
  (∀ candidate ∈ cs, (CBivariate.toPoly Q).eval (toPolynomial candidate) = 0) ∧
  ∀ f : K[X], (CBivariate.toPoly Q).eval f = 0 → (f = 0 ∨ f.natDegree < d) →
    ∃ candidate ∈ cs, toPolynomial candidate = f

theorem initial_correct [Fintype K] (q t : Nat) (points : Array (K × K))
    (hs : points.size = 1048576) (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range (1025 * 112)} → Fin t → K × K)
    (cs : List (List K)) (hout : initial q t points hs H = some cs) :
    ∃ Q, GSConcreteInterpolation.initial points = some Q ∧ Candidates Q 1025 cs := by
  obtain ⟨Q, hr, hw⟩ := GSConcreteInterpolation.initial_exists points hs
  have hc := GSConcreteInterpolation.initial_state_contract points hs Q hr
  have hres : (RRFixedTapeRecovery.recover 112 q t 1025
      (GSConcreteInterpolation.initialState Q) hc.2.1 hc.2.2 H).1 = some cs := by
    simpa only [initial_eq_recovery q t points hs Q hr H] using hout
  have hcan := RRFixedTapeRecovery.recover_correct 112 q t 1025
    (GSConcreteInterpolation.initialState Q) hc.2.1 hc.2.2 hq H cs hres
  refine ⟨Q, hr, ?_⟩
  simpa only [CandidateResult, hc.1, Candidates] using hcan

theorem final_correct [Fintype K] (q t : Nat) (points : Array (K × K))
    (hs : points.size = 262144) (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range (256 * 112)} → Fin t → K × K)
    (cs : List (List K)) (hout : final q t points hs H = some cs) :
    ∃ Q, GSConcreteInterpolation.final points = some Q ∧ Candidates Q 256 cs := by
  obtain ⟨Q, hr, hw⟩ := GSConcreteInterpolation.final_exists points hs
  have hc := GSConcreteInterpolation.final_state_contract points hs Q hr
  have hres : (RRFixedTapeRecovery.recover 112 q t 256
      (GSConcreteInterpolation.finalState Q) hc.2.1 hc.2.2 H).1 = some cs := by
    simpa only [final_eq_recovery q t points hs Q hr H] using hout
  have hcan := RRFixedTapeRecovery.recover_correct 112 q t 256
    (GSConcreteInterpolation.finalState Q) hc.2.1 hc.2.2 hq H cs hres
  refine ⟨Q, hr, ?_⟩
  simpa only [CandidateResult, hc.1, Candidates] using hcan

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
  simpa only [initial_eq_recovery q t points hs Q hr] using hm

theorem final_abort_le (q t : Nat) (points : Array (K × K))
    (hs : points.size = 262144) (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    mean (fun H : {i : Nat // i ∈ Finset.range (256 * 112)} → Fin t → K × K =>
      abortIndicator (final q t points hs H)) ≤ (256 : ℚ) * 112 * (1/2)^t := by
  obtain ⟨Q, hr, hw⟩ := GSConcreteInterpolation.final_exists points hs
  have hc := GSConcreteInterpolation.final_state_contract points hs Q hr
  have hm := RRFixedTapeRecovery.recover_abort_le 112 q t 256
    (GSConcreteInterpolation.finalState Q) hc.2.1 hc.2.2 hq hodd
  simpa only [final_eq_recovery q t points hs Q hr] using hm

#print axioms initial
#print axioms final
#print axioms initial_correct
#print axioms final_correct
#print axioms initial_abort_le
#print axioms final_abort_le
end
end AspisR1.GSConcreteRootRecovery
