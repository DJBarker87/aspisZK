import CuSavingsLibraSourceControl

/-! Successful ordered-builder traversal under a local, index-sensitive
callback invariant. All callback bodies remain source computations. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.CuSavingsLibraSourceBuilder
open CuSavingsArrayBuilder

/-- The output relation may depend on the emitted index; the closure invariant
records all mutable captures after applying the source callback handback. -/
theorem cells_success {T F : Type} (inst : core.ops.function.FnMut F Usize T)
    (P : Nat → F → Prop) (V : Nat → T → Prop) (bound : Nat)
    (hstep : ∀ j state index, j<bound → index.val=j → P j state →
      ∃ value state1, inst.call_mut state index=.ok (value,state1) ∧
        V j value ∧ P (j+1) state1)
    (n : Nat) (start : Usize) (state : F) (hP : P start.val state)
    (hbound : start.val+n≤bound) (hfit : bound<Usize.size) :
    ∃ values finalState,
      cells inst n start state=.ok (values,finalState) ∧
      (∀ i (hi : i<n), V (start.val+i)
        (values.val[i]'(by rw [values.property];exact hi))) ∧
      P (start.val+n) finalState := by
  induction n generalizing start state with
  | zero =>
    refine ⟨⟨[],rfl⟩,state,rfl,?_,?_⟩
    · intro i hi;omega
    · simpa only [Nat.add_zero] using hP
  | succ n ih =>
    have hj : start.val<bound := by omega
    obtain ⟨value,state1,hcall,hV,hP1⟩ := hstep start.val state start hj rfl hP
    obtain ⟨next,hnext,hval⟩ := WP.spec_imp_exists
      (UScalar.add_spec start 1#usize (by scalar_tac))
    have hnval : next.val=start.val+1 := by simpa only [UScalar.ofNatCore_val_eq] using hval
    have hpnext : P next.val state1 := by simpa only [hnval] using hP1
    obtain ⟨rest,finalState,hrest,hvalues,hfinal⟩ := ih next state1 hpnext (by omega)
    let values : {xs : List T // xs.length=n+1} :=
      ⟨value::rest.val,by simp only [List.length_cons,rest.property]⟩
    refine ⟨values,finalState,?_,?_,?_⟩
    · simp only [cells,hcall,hnext,hrest,bind_tc_ok,values]
    · intro i hi
      cases i with
      | zero => simpa only [values,List.getElem_cons_zero,Nat.add_zero] using hV
      | succ i =>
        have hir : i<n := by omega
        have hv := hvalues i hir
        simpa only [values,List.getElem_cons_succ,hnval,Nat.succ_eq_add_one,Nat.add_assoc,
          Nat.add_comm 1 i] using hv
    · have he : next.val+n=start.val+(n+1) := by omega
      simpa only [he] using hfinal

#print axioms cells_success
end AspisR1.CuSavingsLibraSourceBuilder
