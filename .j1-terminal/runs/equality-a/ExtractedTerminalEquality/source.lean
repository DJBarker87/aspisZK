import AspisR1TerminalValidator.Funs

/-! Reflection of the actual homogeneous array comparisons used by the terminal
validator. Symbolic list equality is reused; no concrete array is normalized. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP

namespace AspisR1TerminalValidator.TerminalEquality

theorem array_eq_value {α : Type} [DecidableEq α] {n : Usize}
    (cmp : core.cmp.PartialEq α α)
    (hne : ∀ x y, cmp.ne x y ⦃ b => b ↔ x ≠ y ⦄)
    (a b : Array α n) :
    core.array.equality.PartialEqArray.eq cmp a b = ok (decide (a = b)) := by
  have hs := core.slice.cmp.PartialEqSlice.eq_homo_spec cmp a.to_slice b.to_slice hne
  change WP.spec (core.array.equality.PartialEqArray.eq cmp a b)
    (fun v => v ↔ a.to_slice = b.to_slice) at hs
  obtain ⟨v, hv, hp⟩ := spec_imp_exists hs
  have he : a.to_slice = b.to_slice ↔ a = b := by
    constructor
    · intro h; apply Subtype.ext; exact congrArg Subtype.val h
    · intro h; exact congrArg Array.to_slice h
  have hp : v ↔ a = b := hp.trans he
  have hv' : v = decide (a = b) := by cases v <;> simp_all
  simpa only [hv'] using hv

theorem array_ne_value {α : Type} [DecidableEq α] {n : Usize}
    (cmp : core.cmp.PartialEq α α)
    (hne : ∀ x y, cmp.ne x y ⦃ b => b ↔ x ≠ y ⦄)
    (a b : Array α n) :
    core.array.equality.PartialEqArray.ne cmp a b = ok (decide (a ≠ b)) := by
  simp only [core.array.equality.PartialEqArray.ne, array_eq_value cmp hne,
    bind_tc_ok, Bool.not_decide]

theorem u8_ne_spec (x y : U8) :
    core.cmp.PartialEqU8.ne x y ⦃ b => b ↔ x ≠ y ⦄ := by
  change WP.spec (ok (decide (x ≠ y))) _
  simp only [WP.spec_ok, decide_eq_true_eq]

theorem m31_ne_spec (x y : aspis_core.field.M31) :
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.ne x y ⦃ b => b ↔ x ≠ y ⦄ := by
  apply core.cmp.PartialEq.ne.trait_default.spec
  change WP.spec (ok (decide (x = y))) _
  simp only [WP.spec_ok, decide_eq_true_eq]

#print axioms array_eq_value
#print axioms array_ne_value
#print axioms u8_ne_spec
#print axioms m31_ne_spec
end AspisR1TerminalValidator.TerminalEquality
