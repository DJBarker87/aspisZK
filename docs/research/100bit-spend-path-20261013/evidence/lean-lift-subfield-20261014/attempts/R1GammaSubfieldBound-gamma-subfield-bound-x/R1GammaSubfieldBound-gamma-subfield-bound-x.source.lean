import R0C.ModuloField
import WideTower

/-! A cardinality adapter for the zero-imaginary slice of the nonzero
WideExact challenge space. This is only a bound in the existing modulo model;
it does not identify that model with a Rust sampler or an FS joint law. -/

set_option autoImplicit false

namespace AspisR1.GammaSubfieldBound

open AspisWideTower
open AspisV8R15.ExactTowerFinite
open AspisV8R15.ExactTowerBase
open R0C.ModuloField
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.SourceDuplexStep

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Wide values whose quadratic-extension coordinate is zero. -/
def bad : Finset WideExact := by
  classical
  exact Finset.univ.filter fun x => x.im = 0

theorem mem_bad (x : WideExact) : x ∈ bad ↔ x.im = 0 := by
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]

attribute [local irreducible] bad

private theorem card_zero_coordinate {Q K : Type} [Fintype K] [DecidableEq K] [Zero K]
    (re im : Q → K) (hinj : Function.Injective (fun x => (re x, im x)))
    (s : Finset Q) (hzero : ∀ x ∈ s, im x = 0) :
    s.card ≤ Fintype.card K := by
  classical
  have hf : Set.InjOn re (↑s : Set Q) := by
    intro x hx y hy hxy
    apply hinj
    exact Prod.ext hxy ((hzero x hx).trans (hzero y hy).symm)
  calc
    s.card = (s.image re).card := (Finset.card_image_iff.mpr hf).symm
    _ ≤ Fintype.card K := Finset.card_le_univ (s.image re)

theorem bad_card : bad.card ≤ Fintype.card QM31Exact := by
  classical
  have hz : ∀ x ∈ bad, x.im = 0 := fun x hx => (mem_bad x).mp hx
  exact card_zero_coordinate (Q := WideExact) (K := QM31Exact)
    (fun x => x.re) (fun x => x.im)
    (by
      intro x y h
      exact QuadraticAlgebra.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
    bad hz

theorem gamma_subfield_density :
    mean (fun s : State => indicator ((gammaNZ s).1 ∈ bad)) ≤
      (Fintype.card QM31Exact : ℚ) * (257 / (256^32 : ℚ)) := by
  have h := gamma_event bad
  have he (s : State) : gamma s ∈ bad ↔ (gammaNZ s).1 ∈ bad := Iff.rfl
  have hmean := mean_congr (fun s => FS.indicator_iff (he s))
  exact hmean.symm.le.trans (h.trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast bad_card) (by positivity)))

#print axioms bad_card
#print axioms gamma_subfield_density

end
end AspisR1.GammaSubfieldBound
