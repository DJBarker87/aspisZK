import R1Z.BuilderStdModels

set_option autoImplicit false
namespace R1Z.BuilderStdModels
open Aeneas Aeneas.Std Result
variable {T C : Type}

theorem indices_bound (n : Std.Usize) (i : Std.Usize) (hi : i ∈ indices n) :
    i.val < n.val := by
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
  simpa only [Std.Usize.ofNatCore_val_eq] using j.isLt

theorem fromFnLoop_pure_on (f : core.ops.function.FnMut C Std.Usize T)
    (g : Std.Usize → T) (is : List Std.Usize) (c : C)
    (h : ∀ i ∈ is, f.call_mut c i = ok (g i, c)) :
    fromFnLoop f is c = ok (is.map g, c) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      apply fromFnLoop_cons
      · exact h i (by simp)
      · exact ih (fun j hj => h j (by simp [hj]))

theorem fromFn_bounded (n : Std.Usize) (f : core.ops.function.FnMut C Std.Usize T)
    (g : Std.Usize → T) (c : C)
    (h : ∀ i, i.val < n.val → f.call_mut c i = ok (g i, c)) :
    fromFn n f c = ok (Aeneas.Std.Array.make n
      ((indices n).map g) (by simp [indices])) := by
  have ht := fromFnLoop_pure_on f g (indices n) c
    (fun i hi => h i (indices_bound n i hi))
  unfold fromFn
  rw [ht]
  simp only [bind_tc_ok]
  have hl : ((indices n).map g).length = n.val := by simp only [List.length_map, indices, List.length_ofFn]
  rw [dif_pos hl]
  rfl

#print axioms indices_bound
#print axioms fromFnLoop_pure_on
#print axioms fromFn_bounded
end R1Z.BuilderStdModels
