import MultiproofConeVecLaws

set_option autoImplicit false
namespace AspisR1.MultiproofConePush
open Aeneas Aeneas.Std Result

theorem push_total {α : Type} (rows : alloc.vec.Vec α) (x : α)
    (bound : rows.val.length+1 ≤ Usize.max) :
    ∃ result, alloc.vec.Vec.push rows x = ok result ∧ result.val = rows.val++[x] := by
  unfold alloc.vec.Vec.push
  simp only [show decide (rows.val.length+1≤Usize.max)=true from decide_eq_true bound,
    Bool.or_true,↓reduceDIte]
  exact ⟨_,rfl,List.concat_eq_append⟩

#print axioms push_total
end AspisR1.MultiproofConePush
