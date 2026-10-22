import MultiproofConeCanonical

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeByteEquality
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical
attribute [local instance] Classical.propDecidable

theorem decode_injective : Function.Injective AspisV8R19.SqueezeOracleBridge.decodeByte := by
  intro x y h
  apply UScalar.eq_of_val_eq
  exact congrArg Fin.val h

theorem bytes_injective : Function.Injective bytesOf := by
  intro xs ys h
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      have parts := List.cons.inj h
      have heads := decode_injective parts.1
      have tails := ih parts.2
      rw [heads,tails]

private theorem u8_ne (x y : U8) :
    core.cmp.PartialEqU8.ne x y ⦃ b => b ↔ x ≠ y ⦄ := by
  change WP.spec (ok (decide (x ≠ y))) _
  simp only [WP.spec_ok, decide_eq_true_eq]

theorem array_eq_total {n : Usize} (a b : Array U8 n) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b = ok (decide (a=b)) := by
  have spec := core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU8
    a.to_slice b.to_slice u8_ne
  change WP.spec (core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b)
    (fun v => v ↔ a.to_slice = b.to_slice) at spec
  obtain ⟨v,hv,he⟩ := WP.spec_imp_exists spec
  rw [hv]
  have hab : a.to_slice = b.to_slice ↔ a = b := by
    constructor
    · intro h; exact Subtype.ext (congrArg (fun s : Slice U8 => s.val) h)
    · intro h; subst b; rfl
  have ve : v = decide (a=b) := by cases v <;> simp_all
  rw [ve]

theorem array_ne_total {n : Usize} (a b : Array U8 n) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a b = ok (decide (a≠b)) := by
  unfold core.array.equality.PartialEqArray.ne
  rw [array_eq_total]
  simp only [bind_tc_ok]
  by_cases h : a=b <;> simp [h]

#print axioms decode_injective
#print axioms bytes_injective
#print axioms u8_ne
#print axioms array_eq_total
#print axioms array_ne_total
end AspisR1.MultiproofConeByteEquality
end
