import Port4C_QueryStd

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_FromFn
open Aeneas Aeneas.Std Result
variable {T C : Type}

theorem loop (n : Usize) (f : core.ops.function.FnMut C Usize T)
    (g : Usize → T) (is : List Usize) (c : C)
    (bounds : ∀ i ∈ is, i.val<n.val)
    (callback : ∀ c i, i.val<n.val → f.call_mut c i=ok (g i,c)) :
    OraclePortStdBuilder.fromFnLoop f is c=ok (is.map g,c) := by
  induction is generalizing c with
  | nil => rfl
  | cons i is ih =>
    have head := callback c i (bounds i (by simp))
    have tail := ih c (fun j hj => bounds j (by simp; exact Or.inr hj))
    simp only [OraclePortStdBuilder.fromFnLoop,head,tail,bind_tc_ok,List.map_cons]

theorem indices_bound (n i : Usize) (member : i ∈ OraclePortStdBuilder.indices n) : i.val<n.val := by
  simp only [OraclePortStdBuilder.indices,List.mem_ofFn] at member
  obtain ⟨j,same⟩ := member
  subst i
  exact j.isLt

/-- A bounded FnMut specification is sufficient; no assertion about invalid
usize callback arguments is required by this std model. -/
theorem total (n : Usize) (f : core.ops.function.FnMut C Usize T)
    (g : Usize → T) (c : C)
    (callback : ∀ c i, i.val<n.val → f.call_mut c i=ok (g i,c)) :
    OraclePortStdBuilder.fromFn n f c =
      ok (Array.make n ((OraclePortStdBuilder.indices n).map g)
        (by simp [OraclePortStdBuilder.indices])) := by
  unfold OraclePortStdBuilder.fromFn
  rw [loop n f g _ c (indices_bound n) callback,bind_tc_ok]
  simp only [List.length_map,OraclePortStdBuilder.indices,List.length_ofFn,dif_pos rfl]
  rfl

#print axioms loop
#print axioms indices_bound
#print axioms total
end AspisR1.Port4C_FromFn
end
