import FJb_BuilderSelected
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_BuilderTotal
open Aeneas Aeneas.Std Result
theorem loop {T C : Type} (f : core.ops.function.FnMut C Usize T)
    (is : List Usize) (c : C)
    (stable : ∀ i∈is,∃ x,f.call_mut c i=ok (x,c)) :
    ∃ xs,OraclePortStdBuilder.fromFnLoop f is c=ok (xs,c) ∧ xs.length=is.length := by
  induction is with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons i is ih =>
    obtain ⟨x,hx⟩ := stable i (by simp)
    obtain ⟨xs,hxs,hlen⟩ := ih (by intro i hi;exact stable i (by simp [hi]))
    refine ⟨x::xs,?_,by simp only [List.length_cons,hlen]⟩
    simp only [OraclePortStdBuilder.fromFnLoop,hx,hxs,bind_tc_ok]

theorem value {T C : Type} (N : Usize) (copy : core.marker.Copy T)
    (f : core.ops.function.FnMut C Usize T) (dummy : T) (c : C)
    (stable : ∀ i : Usize,i.val < N.val → ∃ x,f.call_mut c i=ok (x,c)) :
    ∃ out,FIq_Native.array_from_fn_copy N copy f dummy c=ok out := by
  obtain ⟨xs,hxs,hlen⟩ := loop f (OraclePortStdBuilder.indices N) c (by
    intro i hi
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hi
    subst i
    apply stable
    simpa using j.isLt)
  have hn : xs.length=N.val := by simpa only [OraclePortStdBuilder.indices,List.length_ofFn] using hlen
  refine ⟨⟨xs,hn⟩,?_⟩
  unfold FIq_Native.array_from_fn_copy OraclePortStdBuilder.fromFn
  rw [hxs]
  simp only [bind_tc_ok,dif_pos hn]
#print axioms loop
#print axioms value
end AspisR1.FJb_BuilderTotal
end
