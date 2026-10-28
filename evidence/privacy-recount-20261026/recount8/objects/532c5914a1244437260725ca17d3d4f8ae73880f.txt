import R0Z.HonestValidity
import R0Z.HvzkV

/-! J0c (LOG D40.3): the LogUp pole mass of one attempt.  `¬ NoPole t λ χ`
puts `χ` in `poleSet t λ`, at most 4·|active rows| ≤ 4096 values; under the
named sampler premise `Sem1Uniform draw Q` (χ = sem 1 uniform on Q values
given λ = sem 0; for R1, K₄ = QM31 and Q = p⁴) one attempt's pole mass is at
most 4096 / Q.  No Lean lemma fixes the law of the FS challenge draw
(FsGood.lean header: the alpha-row law "is not chosen here"; R0P MaskD2.lean
`uniform_point_mass` is for an abstract uniform type), so the premise is a
named hypothesis. -/
set_option autoImplicit false
noncomputable section

namespace R1Z.PoleMassR1
open R0P R0Z.JointView R0Z.FsStatement R0Z.Shift R0Z.FsGood R0Z.FsAbort R0Z.HvzkV
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ### The pole mass -/

/-- The copy-active rows (kept opaque: never evaluated). -/
@[irreducible] def activeRows : Finset (Fin 1024) :=
  Finset.univ.filter (fun b : Fin 1024 => CopyActiveRow b)

theorem mem_activeRows (b : Fin 1024) (hb : CopyActiveRow b) : b ∈ activeRows := by
  unfold activeRows
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩

theorem activeRows_card_le : activeRows.card ≤ 1024 := by
  unfold activeRows
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])

/-- The four LogUp values of one active row and slot (producer or consumer). -/
def poleValue (t : Trace K) (lam : K) (p : Fin 1024 × Fin 2 × Bool) : K :=
  cond p.2.2 (copyRowValues t lam p.1 CopyLink.producer p.2.1)
    (copyRowValues t lam p.1 CopyLink.consumer p.2.1)

/-- All producer and consumer LogUp values of the active rows. -/
@[irreducible] def poleSet (t : Trace K) (lam : K) : Finset K :=
  (activeRows ×ˢ (Finset.univ : Finset (Fin 2 × Bool))).image (poleValue t lam)

theorem poleValue_mem (t : Trace K) (lam : K) (p : Fin 1024 × Fin 2 × Bool)
    (hp : CopyActiveRow p.1) : poleValue t lam p ∈ poleSet t lam := by
  unfold poleSet
  exact Finset.mem_image_of_mem (poleValue t lam)
    (Finset.mem_product.2 ⟨mem_activeRows p.1 hp, Finset.mem_univ _⟩)

theorem mem_poleSet_of_not_noPole (t : Trace K) (lam chi : K)
    (hn : ¬ R0Z.HonestValidity.NoPole t lam chi) : chi ∈ poleSet t lam := by
  by_contra hc
  apply hn
  intro b hb s
  constructor
  · intro he
    apply hc
    have hm := poleValue_mem t lam (b, s, true) hb
    have hv : poleValue t lam (b, s, true) = chi := he.symm
    rw [hv] at hm
    exact hm
  · intro he
    apply hc
    have hm := poleValue_mem t lam (b, s, false) hb
    have hv : poleValue t lam (b, s, false) = chi := he.symm
    rw [hv] at hm
    exact hm

theorem poleSet_card_le (t : Trace K) (lam : K) :
    (poleSet t lam).card ≤ 4 * activeRows.card := by
  unfold poleSet
  -- Memory (J0d probes 3879/3880): the former `rw [...]; omega` closing of this
  -- lemma alone cost ≈440 MB over the import baseline; every step here closes
  -- syntactically, so nothing is asked to reduce `activeRows.card`.
  have hu : (Finset.univ : Finset (Fin 2 × Bool)).card = 4 := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  calc _ ≤ (activeRows ×ˢ (Finset.univ : Finset (Fin 2 × Bool))).card := Finset.card_image_le
    _ = activeRows.card * 4 := by rw [Finset.card_product, hu]
    _ = 4 * activeRows.card := Nat.mul_comm _ _

theorem poleSet_card_le_4096 (t : Trace K) (lam : K) : (poleSet t lam).card ≤ 4096 :=
  (poleSet_card_le t lam).trans (Nat.mul_le_mul_left 4 activeRows_card_le)

/-- Sampler premise (HYP): `χ = sem 1` is uniform on a set of `Q` values given
`λ = sem 0` (for R1: K₄ = QM31, `Q = p⁴`), in the upper-bound form used here:
for any `λ`-indexed family of at most `m` values, the draw hits it with mass at
most `m / Q`. -/
def Sem1Uniform {Coins : Type} [Fintype Coins] (draw : Coins → Challenges K) (Q : ℕ) : Prop :=
  ∀ (S : K → Finset K) (m : ℕ), (∀ l, (S l).card ≤ m) →
    eventMass (fun c => (draw c).sem 1 ∈ S ((draw c).sem 0)) ≤ (m : ℚ) / Q

/-- One attempt's pole mass for a fixed trace. -/
theorem pole_mass_le {Coins : Type} [Fintype Coins] (draw : Coins → Challenges K) (Q : ℕ)
    (hU : Sem1Uniform draw Q) (t : Trace K) :
    eventMass (fun c => ¬ R0Z.HonestValidity.NoPole t ((draw c).sem 0) ((draw c).sem 1)) ≤
      (4096 : ℚ) / Q := by
  have h := hU (poleSet t) 4096 (fun l => poleSet_card_le_4096 t l)
  refine (eventMass_mono (fun c => ¬ R0Z.HonestValidity.NoPole t ((draw c).sem 0) ((draw c).sem 1))
    (fun c => (draw c).sem 1 ∈ poleSet t ((draw c).sem 0))
    (fun c hc => mem_poleSet_of_not_noPole t _ _ hc)).trans ?_
  exact_mod_cast h

#print axioms activeRows
#print axioms mem_activeRows
#print axioms activeRows_card_le
#print axioms poleValue
#print axioms poleSet
#print axioms poleValue_mem
#print axioms mem_poleSet_of_not_noPole
#print axioms poleSet_card_le
#print axioms poleSet_card_le_4096
#print axioms Sem1Uniform
#print axioms pole_mass_le
end R1Z.PoleMassR1
