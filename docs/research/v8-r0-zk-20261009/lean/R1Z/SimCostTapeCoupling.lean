import R1Z.SimCostBinaryCoupling
import R1Z.PrivacyR1AcctBasis

/-! Uniform binary-word coupling to the eight ACTUAL protocol mask tapes.
The cardinality bound uses a subtype injection, never enumeration of eligible
cells. Sampling cost here is draws only; field expression evaluation is not
silently included. This supplies input tapes, not a certified ideal prelude. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostTapeCoupling
open R0P R0Z R0Z.FsAbortBounds R0Z.JointView R0Z.MaskLayout R1Z.CouplingR1PBin
  R1Z.SimCostBinarySource R1Z.SimCostBinaryCoupling R1Z.SimCostTruncationBudget
attribute [local instance] Classical.propDecidable
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F

abbrev Coordinates := Fin 8 × (AffCoordinate ⊕ EligibleCell)

def enumerateEquiv {I U : Type} [Fintype I] : (Fin (Fintype.card I) → U) ≃ (I → U) where
  toFun u i := u (Fintype.equivFin I i)
  invFun u i := u ((Fintype.equivFin I).symm i)
  left_inv u := by funext i; dsimp only; rw [Equiv.apply_symm_apply]
  right_inv u := by funext i; dsimp only; rw [Equiv.symm_apply_apply]

def pairTapeEquiv {I J U V : Type} (e : U ≃ V) (N : Nat) :
    (Fin N × (I ⊕ J) → U) ≃ (Fin N → (I → V) × (J → V)) where
  toFun u i := (fun a => e (u (i,Sum.inl a)), fun a => e (u (i,Sum.inr a)))
  invFun t c := match c.2 with
    | .inl a => e.symm ((t c.1).1 a)
    | .inr a => e.symm ((t c.1).2 a)
  left_inv u := by
    funext c
    rcases c with ⟨i,a|a⟩ <;> exact e.symm_apply_apply _
  right_inv t := by
    funext i
    apply Prod.ext <;> funext a <;> exact e.apply_symm_apply _

/-- The retained carrier equivalence maps residue codes to the actual M31
subfield of WideExact used by the protocol basis. -/
def tapeEquiv : (Fin (Fintype.card Coordinates) → Fin 2147483647) ≃ (Fin 8 → Tape K F) :=
  enumerateEquiv.trans (pairTapeEquiv ProverCommitWordCarrier.baseEquiv 8)

def completeTapes (r : Fin (Fintype.card Coordinates) → M31Source 8) : Fin 8 → Tape K F :=
  tapeEquiv (batchComplete 2147483647 8 (Fintype.card Coordinates) r)

theorem tapes_uniform : MP completeTapes := by
  intro f
  have h1 := batch_uniform 2147483647 8 (Fintype.card Coordinates) (fun v => f (tapeEquiv v))
  have h2 := mp_equiv tapeEquiv f
  exact h1.trans h2

theorem aff_agrees (r : Fin (Fintype.card Coordinates) → M31Source 8)
    (h : ¬ bad 8 (Fintype.card Coordinates) r) (i : Fin 8) (a : AffCoordinate) :
    ((words 2147483647 8 (r (Fintype.equivFin Coordinates (i,Sum.inl a))).1).1.map
      ProverCommitWordCarrier.baseEquiv) = some ((completeTapes r i).1 a) := by
  have hh := batch_agrees 8 (Fintype.card Coordinates) r h
    (Fintype.equivFin Coordinates (i,Sum.inl a))
  exact congrArg (Option.map ProverCommitWordCarrier.baseEquiv) hh

theorem eligible_agrees (r : Fin (Fintype.card Coordinates) → M31Source 8)
    (h : ¬ bad 8 (Fintype.card Coordinates) r) (i : Fin 8) (a : EligibleCell) :
    ((words 2147483647 8 (r (Fintype.equivFin Coordinates (i,Sum.inr a))).1).1.map
      ProverCommitWordCarrier.baseEquiv) = some ((completeTapes r i).2 a) := by
  have hh := batch_agrees 8 (Fintype.card Coordinates) r h
    (Fintype.equivFin Coordinates (i,Sum.inr a))
  exact congrArg (Option.map ProverCommitWordCarrier.baseEquiv) hh

theorem sample_count : Fintype.card Coordinates ≤ 417792 := by
  have he : Fintype.card EligibleCell ≤ 29696 := by
    have hb := Fintype.card_subtype_le (fun cell : Fin 29 × Fin 1024 => eligible cell.1 cell.2)
    simpa only [Fintype.card_prod, Fintype.card_fin] using hb
  have ha : Fintype.card AffCoordinate = 22528 := by
    simp only [AffCoordinate, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  simp only [Coordinates, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  omega

theorem sample_count_small : Fintype.card Coordinates ≤ 2^128 :=
  sample_count.trans (by norm_num)

theorem tape_failure_mass : mass (bad 8 (Fintype.card Coordinates)) ≤ 1/(2:ℚ)^120 :=
  (eight_failure_budget _).trans (extra_mass_small _ sample_count_small)

theorem tape_source_draws (r : Fin (Fintype.card Coordinates) → M31Source 8) :
    ∑ i, (words 2147483647 8 (r i).1).2 ≤ 3342336 := by
  exact (batch_draws 8 _ r).trans (by have hh := sample_count; omega)

/-- Every bounded observer of the actual eight protocol tapes is transported
at the explicit truncation budget, given off-failure implementation agreement. -/
theorem tape_observer_transfer
    (real : (Fin (Fintype.card Coordinates) → M31Source 8) → ℚ)
    (ideal : (Fin 8 → Tape K F) → ℚ)
    (hr : ∀ r, 0 ≤ real r ∧ real r ≤ 1) (hi : ∀ t, 0 ≤ ideal t ∧ ideal t ≤ 1)
    (ha : ∀ r, ¬ bad 8 (Fintype.card Coordinates) r → real r = ideal (completeTapes r)) :
    |mean real - mean ideal| ≤ 1/(2:ℚ)^120 := by
  have hb := R0Z.FsAbort.until_bad real (fun r => ideal (completeTapes r)) hr
    (fun r => hi _) (bad 8 (Fintype.card Coordinates)) ha
  rw [tapes_uniform ideal] at hb
  exact hb.trans tape_failure_mass

#print axioms enumerateEquiv
#print axioms pairTapeEquiv
#print axioms tapeEquiv
#print axioms tapes_uniform
#print axioms aff_agrees
#print axioms eligible_agrees
#print axioms sample_count
#print axioms sample_count_small
#print axioms tape_failure_mass
#print axioms tape_source_draws
#print axioms tape_observer_transfer
end R1Z.SimCostTapeCoupling
