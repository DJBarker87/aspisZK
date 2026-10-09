import R0C.SemStatement
import R0C.Counting
import AspisFormal.CircleGroupCardinality

/-! Exact BaseRational count and the two ideal uniform-circle rows.
These are laws on Point K, not on byte states or a claimed source sampler. -/
set_option autoImplicit false
namespace R0C.CircleRows
open AspisR0.Chord AspisR0.ChordGeometry AspisCircleGroupOrder
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
noncomputable section
attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [Algebra (ZMod P) K]

/-- Inclusion of the WHOLE base-field circle, not just the evaluation domain. -/
def baseLift (z : C) : Point K :=
  ⟨(algebraMap (ZMod P) K z.val.1, algebraMap (ZMod P) K z.val.2), by
    have h := congrArg (algebraMap (ZMod P) K) z.property
    simpa only [OnCircle, map_add, map_pow, map_one] using h⟩

omit [Fintype K] in
theorem baseLift_injective : Function.Injective (baseLift (K := K)) := by
  intro z w h
  apply Subtype.ext
  apply Prod.ext
  · apply (algebraMap (ZMod P) K).injective
    exact congrArg (fun q : Point K => q.val.1) h
  · apply (algebraMap (ZMod P) K).injective
    exact congrArg (fun q : Point K => q.val.2) h

omit [Fintype K] in
theorem baseLift_rational (z : C) : BaseRational (baseLift (K := K) z) :=
  ⟨⟨z.val.1, rfl⟩, ⟨z.val.2, rfl⟩⟩

omit [Fintype K] in
theorem rational_iff_lift (z : Point K) :
    BaseRational z ↔ ∃ b : C, baseLift b = z := by
  constructor
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    have hc : OnCircle (x,y) := by
      apply (algebraMap (ZMod P) K).injective
      simpa only [OnCircle, map_add, map_pow, map_one, hx, hy] using z.property
    exact ⟨⟨(x,y),hc⟩, Subtype.ext (Prod.ext hx hy)⟩
  · rintro ⟨b,rfl⟩
    exact baseLift_rational b

def rationalEquiv : C ≃ {z : Point K // BaseRational z} :=
  Equiv.ofBijective (fun b => ⟨baseLift b, baseLift_rational b⟩) ⟨
    fun _ _ h => baseLift_injective (congrArg Subtype.val h),
    fun z => by
      obtain ⟨b,hb⟩ := (rational_iff_lift z.val).mp z.property
      exact ⟨b, Subtype.ext hb⟩⟩

theorem baseRational_card : Fintype.card {z : Point K // BaseRational z} = 2^31 :=
  (Fintype.card_congr (rationalEquiv (K := K))).symm.trans card_C_eq

/-- First-row upper bound under the uniform law on the full circle: the
rational points and the second row's fallback. -/
theorem z0_density_le (fallback1 : Point K) :
    mean (fun z : Point K => indicator (SemStatement.z0Bad fallback1 z)) ≤
      (2^31+1 : ℚ) / Fintype.card (Point K) := by
  letI : Nonempty (Point K) := ⟨fallback1⟩
  have h := Counting.mean_or_eq_le (BaseRational (K := K)) fallback1
  simpa only [SemStatement.z0Bad, baseRational_card, Nat.cast_pow, Nat.cast_ofNat] using h

/-- Second-row upper bound, including equality with the preceding challenge. -/
theorem z1_density_le (z0 : Point K) :
    mean (fun z : Point K => indicator (SemStatement.z1Bad z0 z)) ≤
      (2^31+1 : ℚ) / Fintype.card (Point K) := by
  letI : Nonempty (Point K) := ⟨z0⟩
  have h := Counting.mean_or_eq_le (BaseRational (K := K)) z0
  simpa only [SemStatement.z1Bad, baseRational_card, Nat.cast_pow, Nat.cast_ofNat] using h

omit [Fintype K] in
/-- Absence of the two counted events supplies precisely the old Stmt fields. -/
theorem chord_conditions (fallback1 z0 z1 : Point K)
    (h0 : ¬ SemStatement.z0Bad fallback1 z0) (h1 : ¬ SemStatement.z1Bad z0 z1) :
    z0 ≠ z1 ∧ ¬ BaseRational z0 ∧ ¬ BaseRational z1 := by
  exact ⟨fun h => h1 (Or.inr h.symm), fun h => h0 (Or.inl h), fun h => h1 (Or.inl h)⟩

#print axioms baseRational_card
#print axioms z0_density_le
#print axioms z1_density_le
#print axioms chord_conditions
end
end R0C.CircleRows
