import MultiproofConeRef.Funs

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeLeaf
attribute [local instance] Classical.propDecidable
open Aeneas Aeneas.Std Result
open MultiproofConeRef

private theorem u8_ne (x y : U8) :
    core.cmp.PartialEqU8.ne x y ⦃ b => b ↔ x ≠ y ⦄ := by
  change WP.spec (ok (decide (x ≠ y))) _
  simp only [WP.spec_ok, decide_eq_true_eq]

/-- Equality of all 32 digest bytes, with total checked execution. -/
theorem digest_eq_total (a b : Array U8 32#usize) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b =
      ok (decide (a = b)) := by
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
  have ve : v = decide (a=b) := by
    cases v <;> simp_all
  rw [ve]

@[local step]
theorem digest_eq_spec (a b : Array U8 32#usize) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b ⦃ v => v ↔ a=b ⦄ := by
  rw [digest_eq_total]
  simp only [WP.spec_ok, decide_eq_true_eq]

/-- The complete extracted leaf insertion is outer-success total on every
scratch prefix that has room for the next reached leaf. Inner none retains
ordinary unequal-duplicate rejection. -/
theorem leaf_step_total (s : reference.Scratch) (index : U32)
    (leaf : Array U8 32#usize) (hn : s.n.val < 16) :
    ∃ out, reference.leaf_step s index leaf = ok out := by
  have spec : reference.leaf_step s index leaf ⦃ _ => True ⦄ := by
    unfold reference.leaf_step
    step* <;> scalar_tac
  exact WP.spec_imp_exists spec |>.imp (fun out h => h.1)

#print axioms u8_ne
#print axioms digest_eq_total
#print axioms digest_eq_spec
#print axioms leaf_step_total
end AspisR1.MultiproofConeLeaf
end
