import Wide.GRSConversion
import Mathlib.LinearAlgebra.Lagrange

set_option autoImplicit false

namespace AspisWide.InitialInverse
open Polynomial
open AspisWide.GRSConversion
noncomputable section

variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K] [DecidableEq K] [NeZero (2 : K)]

/-- Interpolate the inverse stereographic transform from a fixed finite set
of nodes. This avoids enumerating the extension field. -/
noncomputable def decodeFractionalLift
    (d : Nat) (nodes : Fin (d + 1) → K)
    (havoid : ∀ i, nodes i ≠ -1) (q : K[X]) : K[X] :=
  Lagrange.interpolate Finset.univ nodes fun i =>
    q.eval ((1 - nodes i) / (1 + nodes i)) *
      ((1 + ((1 - nodes i) / (1 + nodes i))) ^ d)⁻¹

private theorem fractionalLift_eval_ratio
    (d : Nat) (p : K[X]) (hp : p.natDegree ≤ d) (t : K)
    (hden : 1 + t ≠ 0) :
    (AspisV5FriCircleEncoderDistance.fractionalLift d p).eval t =
      p.eval ((1 - t) / (1 + t)) * (1 + t) ^ d := by
  rw [AspisV5FriCircleEncoderDistance.fractionalLift_eval]
  exact AspisV5FriCircleEncoderDistance.mobiusLift_eval_div
    d p hp (1 - t) (1 + t) hden

theorem decodeFractionalLift_fractionalLift
    (d : Nat) (nodes : Fin (d + 1) → K)
    (hnodes : Function.Injective nodes)
    (havoid : ∀ i, nodes i ≠ -1)
    (p : K[X]) (hp : p.natDegree ≤ d) :
    decodeFractionalLift d nodes havoid
      (AspisV5FriCircleEncoderDistance.fractionalLift d p) = p := by
  classical
  apply (Lagrange.eq_interpolate_of_eval_eq
    (fun i =>
      (AspisV5FriCircleEncoderDistance.fractionalLift d p).eval
          ((1 - nodes i) / (1 + nodes i)) *
        ((1 + ((1 - nodes i) / (1 + nodes i))) ^ d)⁻¹)
    hnodes.injOn ?_ ?_).symm
  · by_cases hp0 : p = 0
    · simp [hp0]
    · calc
        p.degree ≤ (p.natDegree : WithBot Nat) := Polynomial.degree_le_natDegree
        _ ≤ (d : WithBot Nat) := by exact_mod_cast hp
        _ < ((Finset.univ : Finset (Fin (d + 1))).card : WithBot Nat) := by
          have hc : (Finset.univ : Finset (Fin (d + 1))).card = d + 1 := by simp
          rw [hc]
          exact_mod_cast (show d < d + 1 by omega)
  · intro i hi
    let t := (1 - nodes i) / (1 + nodes i)
    have hinv := AspisV5FriCircleEncoderDistance.fractional_involution
      (nodes i) (havoid i)
    have hplus : 1 + t ≠ 0 := by simpa [t] using hinv.1
    have hback : (1 - t) / (1 + t) = nodes i := by simpa [t] using hinv.2
    have hratio := fractionalLift_eval_ratio d p hp t hplus
    have hratio' :
        (AspisV5FriCircleEncoderDistance.fractionalLift d p).eval t =
          p.eval (nodes i) * (1 + t) ^ d := by rw [hratio, hback]
    change p.eval (nodes i) =
      (AspisV5FriCircleEncoderDistance.fractionalLift d p).eval t *
        ((1 + t) ^ d)⁻¹
    rw [hratio']
    have hpow : (1 + t) ^ d ≠ 0 := pow_ne_zero _ hplus
    field_simp [hpow]

#print axioms decodeFractionalLift_fractionalLift
end
end AspisWide.InitialInverse
