import NDO_JFu_BoundedBuilder
import RPv_FIw_ArrayValue
set_option autoImplicit false
namespace AspisR1.JFy_BoundedCanonical
open Aeneas Aeneas.Std Result

theorem loop {T F : Type} (P : T → Prop) (fn : core.ops.function.FnMut F Usize T)
    (state : F) (is : List Usize)
    (calls : ∀ i ∈ is,∃ v,fn.call_mut state i=ok (v,state) ∧ P v) :
    ∃ xs,OraclePortStdBuilder.fromFnLoop fn is state=ok (xs,state) ∧
      xs.length=is.length ∧ ∀ x ∈ xs,P x := by
  induction is with
  | nil => exact ⟨[],rfl,rfl,by simp⟩
  | cons i is ih =>
    obtain ⟨v,call,hv⟩ := calls i (by simp)
    obtain ⟨xs,tail,length,hxs⟩ := ih (by intro j hj;exact calls j (by simp only [List.mem_cons];exact Or.inr hj))
    refine ⟨v::xs,?_,by simp only [List.length_cons,length],?_⟩
    · simp only [OraclePortStdBuilder.fromFnLoop,call,bind_tc_ok,Aeneas.Std.uncurry,tail]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hv
      · exact hxs x hx
#print axioms loop

theorem source {T F : Type} (P : T → Prop) (n : Usize) (fn : core.ops.function.FnMut F Usize T)
    (state : F) (calls : ∀ i : Usize,i.val<n.val → ∃ v,fn.call_mut state i=ok (v,state) ∧ P v) :
    ∃ out,OraclePortStdBuilder.fromFn n fn state=ok out ∧ ∀ x∈out.val,P x := by
  have bounded : ∀ i ∈ OraclePortStdBuilder.indices n,∃ v,fn.call_mut state i=ok (v,state) ∧ P v := by
    intro i hi
    unfold OraclePortStdBuilder.indices at hi
    rw [List.mem_ofFn] at hi
    obtain ⟨j,rfl⟩ := hi
    exact calls _ j.isLt
  obtain ⟨xs,call,length,canonical⟩ := loop P fn state (OraclePortStdBuilder.indices n) bounded
  have size : xs.length=n.val := by
    simpa only [OraclePortStdBuilder.indices,List.length_ofFn] using length
  refine ⟨⟨xs,size⟩,?_,canonical⟩
  unfold OraclePortStdBuilder.fromFn
  rw [call,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,dif_pos size]
#print axioms source
end AspisR1.JFy_BoundedCanonical
