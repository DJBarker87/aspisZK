import R0C.ModuloField
import WideTower

/-! A cardinality adapter for the zero-imaginary slice of the nonzero
WideExact challenge space. This is only a bound in the existing modulo model;
it does not identify that model with a Rust sampler or an FS joint law. -/

set_option autoImplicit false
set_option maxRecDepth 16384

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
  let subtypeBad := {x : WideExact // x ∈ bad}
  let f : subtypeBad → QM31Exact := fun x => x.1.re
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hx' := x.2
    have hy' := y.2
    rw [bad, Finset.mem_filter] at hx' hy'
    apply QuadraticAlgebra.ext
    · exact hxy
    · exact hx'.2.trans hy'.2.symm
  have hcard : Fintype.card subtypeBad ≤ Fintype.card QM31Exact :=
    Fintype.card_le_of_injective f hf
  simpa only [Finset.card, subtypeBad] using hcard

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
