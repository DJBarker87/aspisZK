import R0C.Counting
import R0FS.V2

/-! The FIRST sampler law is impossible for every total one-block sampler.
The proof counts over abstract finite types, then uses cardinality theorems.
No universe of State or Addr is enumerated or unfolded. -/
set_option autoImplicit false
namespace R0C.SamplerObstruction
open FS
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.SourceDuplexStep AspisV8R19.UniformStateFirstHit
open AspisWideTower AspisCircleGroupOrder
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A nonzero field-valued total sampler with the stated gamma bound must
have equally sized fibers over every nonzero field element. -/
theorem nonzero_card_dvd {A E : Type} [Fintype A] [Nonempty A]
    [Field E] [Fintype E] (f : A → R0FS.Chal E)
    (hn : ∀ a, ∃ c, f a = .field c ∧ c ≠ 0)
    (hm : ∀ c : E, mean (fun a => indicator (f a = .field c)) ≤
      1 / ((Fintype.card E : ℚ) - 1)) :
    Fintype.card E - 1 ∣ Fintype.card A := by
  classical
  let g : A → {c : E // c ≠ 0} := fun a =>
    ⟨Classical.choose (hn a), (Classical.choose_spec (hn a)).2⟩
  have hg (a : A) : f a = .field (g a).val := (Classical.choose_spec (hn a)).1
  have hc : Fintype.card {c : E // c ≠ 0} = Fintype.card E - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have hcast : (Fintype.card {c : E // c ≠ 0} : ℚ) = (Fintype.card E : ℚ) - 1 := by
    rw [hc, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero), Nat.cast_one]
  haveI : Nonempty {c : E // c ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  rw [← hc]
  apply Counting.card_dvd_of_point_mass_le g
  intro c
  rw [hcast]
  have he : ∀ a, g a = c ↔ f a = .field c.val := by
    intro a
    rw [hg]
    constructor
    · intro h; rw [h]
    · intro h; exact Subtype.ext (R0FS.Chal.field_injective h)
  rw [mean_congr (fun a => indicator_iff (he a))]
  exact hm c.val

/-- Small modular arithmetic, not normalization of any finite universe. -/
theorem wide_nonzero_not_dvd_state : ¬ (P^8 - 1) ∣ 256^32 := by
  have hthree : 3 ∣ P^8 - 1 := by norm_num [P]
  have hn : ¬ 3 ∣ 256^32 := by norm_num
  exact fun h => hn (dvd_trans hthree h)

/-- Refutation of the existing fixed-interface law, for ANY encoding, labels,
initial state and one-block challenge function. No alternative law is installed. -/
theorem noSamplerLawsD {Pf : Type} {L : Nat}
    {Sfield : Fin 29 → Subfield WideExact}
    (p : FS2.Duplex.Params (R0FS.Msg WideExact) (R0FS.Chal WideExact) L)
    (msg : Pf → Nat → R0FS.Msg WideExact) :
    ¬ R0FS.V2.SamplerLawsD (Sfield := Sfield) p msg := by
  intro hs
  have hn := hs.nonzero
  have hm := hs.gamma
  simp only [R0FS.V2.params1] at hn hm
  have hd := nonzero_card_dvd (A := State) (p.σ 0) hn hm
  rw [wideExact_card, state_card] at hd
  exact wide_nonzero_not_dvd_state hd

#print axioms nonzero_card_dvd
#print axioms wide_nonzero_not_dvd_state
#print axioms noSamplerLawsD
end
end R0C.SamplerObstruction
