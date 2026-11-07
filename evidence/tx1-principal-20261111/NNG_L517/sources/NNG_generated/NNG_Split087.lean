import NMP_PrepareState
set_option autoImplicit false
namespace AspisR1.NNG_Split087
open Aeneas Aeneas.Std Result

theorem split {T : Type} (s : Slice T) (n : Usize) (bound : n.val≤s.val.length) :
 ∃ (left right : Slice T) (back : Slice T × Slice T → Slice T),
 core.slice.Slice.split_at_mut s n=.ok ((left,right),back) ∧
 left.val=s.val.take n.val ∧ right.val=s.val.drop n.val ∧
 ∀ (a b : Slice T),a.val.length=left.val.length → b.val.length=right.val.length →
   (back (a,b)).val=a.val++b.val := by
 simp only [core.slice.Slice.split_at_mut,dif_pos bound,List.splitAt_eq]
 refine ⟨_,_,_,rfl,rfl,rfl,?_⟩
 intro a b ha hb
 dsimp only
 rw [dif_pos (show a.length=(s.val.take n.val).length ∧ b.length=(s.val.drop n.val).length from ⟨ha,hb⟩)]

/-- The split callbacks reassemble the two actual updated buffers. Dimensions
are preserved by their CLOSED expansion outputs, never assumed byte contents. -/
theorem split_lengths {T : Type} (xs : List T) (n : Nat) (bound : n≤xs.length) :
 (xs.take n).length=n ∧ (xs.drop n).length=xs.length-n := by
 simp only [List.length_take,List.length_drop,Nat.min_eq_left bound]
 trivial
#print axioms split
#print axioms split_lengths
end AspisR1.NNG_Split087
