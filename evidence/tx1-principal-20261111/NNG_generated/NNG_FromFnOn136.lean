import NNG_StdFromFn
set_option autoImplicit false
namespace AspisR1.NNG_FromFnOn136
open Aeneas Aeneas.Std Result OraclePortStdBuilder

/-- Domain-local callback law. The actual standard loop invokes only indices
in this list; no total successful-callback premise is demanded outside it. -/
theorem loop {T C : Type} (f : core.ops.function.FnMut C Usize T)
    (g : Usize → T) (capture : C) (is : List Usize)
    (law : ∀ i ∈ is, f.call_mut capture i = .ok (g i,capture)) :
    fromFnLoop f is capture = .ok (is.map g,capture) := by
  induction is with
  | nil => rfl
  | cons i rest ih =>
    apply fromFnLoop_cons f i rest capture capture capture (g i) (rest.map g)
    · exact law i (List.mem_cons_self)
    · exact ih (fun j hj => law j (List.mem_cons_of_mem i hj))
#print axioms loop

/-- The finite-index builder's list has precisely its declared extent. -/
theorem indices_length (n : Usize) : (indices n).length = n.val := by
  simp only [indices, List.length_ofFn]
#print axioms indices_length

theorem indices_bound (n : Usize) (i : Usize) (hi : i ∈ indices n) : i.val < n.val := by
  unfold indices at hi
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hi
  subst i
  exact j.isLt
#print axioms indices_bound

/-- Domain-local from_fn interpretation, preserving every captured cell.
Only indices actually visited by the standard builder need the callback law. -/
theorem from_fn {T C : Type} (n : Usize) (f : core.ops.function.FnMut C Usize T)
    (g : Usize → T) (capture : C)
    (law : ∀ i ∈ indices n, f.call_mut capture i = .ok (g i,capture)) :
    ∃ value, fromFn n f capture = .ok value ∧ value.val = (indices n).map g := by
  have len : ((indices n).map g).length = n.val := by
    rw [List.length_map, indices_length]
  refine ⟨⟨(indices n).map g,len⟩,?_,rfl⟩
  rw [fromFn,loop f g capture (indices n) law]
  simp only [bind_tc_ok, dif_pos len]
#print axioms from_fn
end AspisR1.NNG_FromFnOn136
