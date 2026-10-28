import RPz7_FIp_Install
set_option autoImplicit false
namespace AspisR1.JFu_BoundedBuilder
open Aeneas Aeneas.Std Result

theorem loop {T F : Type} (fn : core.ops.function.FnMut F Usize T) (state : F) (is : List Usize)
    (calls : ∀ i ∈ is,∃ v,fn.call_mut state i=ok (v,state)) :
    ∃ xs,OraclePortStdBuilder.fromFnLoop fn is state=ok (xs,state) ∧ xs.length=is.length := by
  induction is with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons i is ih =>
    obtain ⟨v,call⟩ := calls i (by simp)
    obtain ⟨xs,tail,length⟩ := ih (by intro j hj;exact calls j (by simp only [List.mem_cons];exact Or.inr hj))
    refine ⟨v::xs,?_,by simp only [List.length_cons,length]⟩
    simp only [OraclePortStdBuilder.fromFnLoop,call,bind_tc_ok,Aeneas.Std.uncurry,tail]

theorem source {T F : Type} (n : Usize) (fn : core.ops.function.FnMut F Usize T) (state : F)
    (calls : ∀ i : Usize,i.val<n.val → ∃ v,fn.call_mut state i=ok (v,state)) :
    ∃ out,OraclePortStdBuilder.fromFn n fn state=ok out := by
  have bounded : ∀ i ∈ OraclePortStdBuilder.indices n,∃ v,fn.call_mut state i=ok (v,state) := by
    intro i hi
    unfold OraclePortStdBuilder.indices at hi
    rw [List.mem_ofFn] at hi
    obtain ⟨j,rfl⟩ := hi
    exact calls _ j.isLt
  obtain ⟨xs,loopCall,length⟩ := loop fn state (OraclePortStdBuilder.indices n) bounded
  have size : xs.length=n.val := by
    simpa only [OraclePortStdBuilder.indices,List.length_ofFn] using length
  refine ⟨⟨xs,size⟩,?_⟩
  unfold OraclePortStdBuilder.fromFn
  rw [loopCall,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,dif_pos size]

#print axioms loop
#print axioms source
end AspisR1.JFu_BoundedBuilder
