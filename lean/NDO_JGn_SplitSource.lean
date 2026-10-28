import NDO_JGn_CurrentPreparation
set_option autoImplicit false
namespace AspisR1.JGn_SplitSource
open Aeneas Aeneas.Std Result

theorem source (input : Slice U8) (n : Usize) (bound : n.val ≤ input.length) :
    ∃ (left right : Slice U8) (back : Slice U8 × Slice U8 → Slice U8),
      core.slice.Slice.split_at_mut input n=ok ((left,right),back) ∧
      left.val=input.val.take n.val ∧ right.val=input.val.drop n.val ∧
      (∀ pair, (back pair).val =
        if pair.1.length=left.length ∧ pair.2.length=right.length then
          pair.1.val++pair.2.val else input.val) := by
  unfold core.slice.Slice.split_at_mut
  erw [dif_pos bound]
  simp only [List.splitAt_eq]
  refine ⟨_,_,_,rfl,rfl,rfl,?_⟩
  intro pair
  split <;> simp_all
#print axioms source
end AspisR1.JGn_SplitSource
