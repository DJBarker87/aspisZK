import R0C.ModuloField
import WideTower

/-! A cardinality adapter for the zero-imaginary slice of the nonzero
WideExact challenge space. This is only a bound in the existing modulo model;
it does not identify that model with a Rust sampler or an FS joint law. -/

set_option autoImplicit false

namespace AspisR1.GammaSubfieldBound

open AspisWideTower
open R0C.ModuloField

/-- Nonzero wide-field values whose quadratic-extension coordinate is zero. -/
def bad : Finset {x : WideExact // x ≠ 0} :=
  Finset.univ.filter fun x => x.1.im = 0

theorem bad_card : bad.card ≤ Fintype.card QM31Exact := by
  let subtypeBad := {x : {x : WideExact // x ≠ 0} // x ∈ bad}
  let f : subtypeBad → QM31Exact := fun x => x.1.1.re
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hx : x.1.1.im = 0 := (Finset.mem_filter.mp x.2).2
    have hy : y.1.1.im = 0 := (Finset.mem_filter.mp y.2).2
    ext
    · exact hxy
    · simp [hx, hy]
  have hcard : Fintype.card subtypeBad ≤ Fintype.card QM31Exact :=
    Fintype.card_le_of_injective f hf
  simpa [subtypeBad, bad] using hcard

theorem gamma_subfield_density :
    mean (fun s : State => indicator (gammaNZ s ∈ bad)) ≤
      (Fintype.card QM31Exact : ℚ) * (257 / (256^32 : ℚ)) := by
  have h := gamma_event bad
  apply h.trans
  apply mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact_mod_cast bad_card

#print axioms bad_card
#print axioms gamma_subfield_density

end AspisR1.GammaSubfieldBound
