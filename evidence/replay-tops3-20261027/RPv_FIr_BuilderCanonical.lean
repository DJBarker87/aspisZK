import RPv_FIr_ArrayRead
import OraclePortStdBuilder
set_option autoImplicit false
namespace AspisR1.FIr_BuilderCanonical
open Aeneas Aeneas.Std Result

theorem loop {T C : Type} (f : core.ops.function.FnMut C Usize T)
    (Inv : C → Prop) (Good : T → Prop)
    (step : ∀ c i x c',Inv c → f.call_mut c i=ok (x,c') → Good x ∧ Inv c')
    (is : List Usize) (c : C) (xs : List T) (last : C)
    (initial : Inv c) (run : OraclePortStdBuilder.fromFnLoop f is c=ok (xs,last)) :
    (∀ x∈xs,Good x) ∧ Inv last := by
  induction is generalizing c xs last with
  | nil =>
    simp only [OraclePortStdBuilder.fromFnLoop,Result.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    refine ⟨?_,initial⟩
    intro x mem
    cases mem
  | cons i is ih =>
    unfold OraclePortStdBuilder.fromFnLoop at run
    obtain ⟨⟨x,c'⟩,called,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨⟨ys,last'⟩,tail,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    have eq := Result.ok.inj run
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    have one := step c i x c' initial called
    have rest := ih c' ys last' one.2 tail
    refine ⟨?_,rest.2⟩
    intro y member
    rcases List.mem_cons.mp member with rfl | mem
    · exact one.1
    · exact rest.1 y mem

theorem fromFn {T C : Type} (n : Usize) (f : core.ops.function.FnMut C Usize T)
    (Inv : C → Prop) (Good : T → Prop)
    (step : ∀ c i x c',Inv c → f.call_mut c i=ok (x,c') → Good x ∧ Inv c')
    (c : C) (out : Array T n) (initial : Inv c)
    (run : OraclePortStdBuilder.fromFn n f c=ok out) : ∀ x∈out.val,Good x := by
  unfold OraclePortStdBuilder.fromFn at run
  obtain ⟨⟨xs,last⟩,called,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only at run
  split at run
  · have same := Result.ok.inj run
    have valEq := congrArg Subtype.val same
    rw [← valEq]
    exact (loop f Inv Good step _ c xs last initial called).1
  · cases run

#print axioms loop
#print axioms fromFn
end AspisR1.FIr_BuilderCanonical
