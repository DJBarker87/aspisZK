import R0C.ModuloField
import WideTower

/-! A cardinality adapter for the zero-imaginary slice of the nonzero
WideExact challenge space. This is only a bound in the existing modulo model;
it does not identify that model with a Rust sampler or an FS joint law. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace AspisR1.GammaSubfieldBound

open AspisWideTower
open AspisV8R15.ExactTowerFinite
open AspisV8R15.ExactTowerBase
open R0C.ModuloField
open R0C.ModuloCounting
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.SourceDuplexStep
noncomputable section

/-- Nonzero wide-field values whose quadratic-extension coordinate is zero. -/
def bad : Finset {x : WideExact // x ≠ 0} :=
  Finset.univ.filter fun x => x.1.im = 0

theorem mem_bad {x : {x : WideExact // x ≠ 0}} : x ∈ bad ↔ x.1.im = 0 := by
  simp [bad]

theorem bad_card : bad.card ≤ Fintype.card QM31Exact := by
  let subtypeBad := {x : {x : WideExact // x ≠ 0} // x ∈ bad}
  let f : subtypeBad → QM31Exact := fun x => x.1.1.re
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hx : x.1.1.im = 0 := by change x.1.1.im = 0 at x.2; exact x.2
    have hy : y.1.1.im = 0 := by change y.1.1.im = 0 at y.2; exact y.2
    apply QuadraticAlgebra.ext
    · exact hxy
    · exact hx.trans hy.symm
  have hcard : Fintype.card subtypeBad ≤ Fintype.card QM31Exact :=
    Fintype.card_le_of_injective f hf
  exact hcard

theorem gamma_subfield_density :
    mean (fun s : State => indicator (gammaNZ s ∈ bad)) ≤
      (Fintype.card QM31Exact : ℚ) * (257 / (256^32 : ℚ)) := by
  have hmass : ∀ y : {x : WideExact // x ≠ 0},
      mean (fun s : State => indicator (gammaNZ s = y)) ≤ 257 / (256^32 : ℚ) := by
    intro y
    have he (s : State) : gamma s = y.1 ↔ gammaNZ s = y :=
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    have hmean := mean_congr (fun s => FS.indicator_iff (he s))
    exact hmean.symm.le.trans (gamma_mass_257 y.1)
  have h := event_mass_le gammaNZ (257 / (256^32 : ℚ)) hmass bad
  exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast bad_card) (by positivity))

#print axioms bad_card
#print axioms gamma_subfield_density

end
end AspisR1.GammaSubfieldBound
