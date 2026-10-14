import R0C.ModuloField
import WideTower

/-! A cardinality adapter for the zero-imaginary slice of the nonzero
WideExact challenge space. This is only a bound in the existing modulo model;
it does not identify that model with a Rust sampler or an FS joint law. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

namespace AspisR1.GammaSubfieldBound

open AspisWideTower
open AspisV8R15.ExactTowerFinite
open AspisV8R15.ExactTowerBase
open R0C.ModuloField
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.SourceDuplexStep

noncomputable section

/-- Wide values whose quadratic-extension coordinate is zero. -/
def bad : Finset WideExact := Finset.univ.filter fun x => x.im = 0

theorem bad_card : bad.card ≤ Fintype.card QM31Exact := by
  classical
  let f : WideExact → QM31Exact := fun x => x.re
  have hf : Set.InjOn f (↑bad : Set WideExact) := by
    intro x hx y hy hxy
    change x ∈ bad at hx
    change y ∈ bad at hy
    have hx0 : x.im = 0 := (Finset.mem_filter.mp hx).2
    have hy0 : y.im = 0 := (Finset.mem_filter.mp hy).2
    apply QuadraticAlgebra.ext
    · exact hxy
    · exact hx0.trans hy0.symm
  calc
    bad.card = (bad.image f).card := (Finset.card_image_iff.mpr hf)
    _ ≤ Finset.univ.card := Finset.card_le_univ _
    _ = Fintype.card QM31Exact := by simp

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
