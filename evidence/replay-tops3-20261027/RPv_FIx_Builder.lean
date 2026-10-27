import RPv_FIw_BuilderValue
import RPu_FIq_FromFn
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_Builder
open Aeneas Aeneas.Std Result

theorem loop {T C V : Type} (f : core.ops.function.FnMut C Usize T)
    (P : T → Prop) (observe : T → V) (model : Usize → V)
    (is : List Usize) (c : C) (xs : List T) (last : C)
    (step : ∀ i∈is,∀ x c',f.call_mut c i=ok (x,c') → P x ∧ observe x=model i ∧ c'=c)
    (run : OraclePortStdBuilder.fromFnLoop f is c=ok (xs,last)) :
    (∀ x∈xs,P x) ∧ xs.map observe=is.map model ∧ last=c := by
  induction is generalizing xs last with
  | nil =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)
    exact ⟨by simp,rfl,rfl⟩
  | cons i is ih =>
    unfold OraclePortStdBuilder.fromFnLoop at run
    obtain ⟨⟨x,c'⟩,call,r1⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨⟨ys,last'⟩,tail,r2⟩ := FIv_Map.bind_success _ _ _ r1
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj r2)
    have one := step i (by simp) x c' call
    have eq := one.2.2
    subst c'
    have rest := ih ys last' (by intro i h;exact step i (by simp [h])) tail
    refine ⟨?_,?_,rest.2.2⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact one.1
      · exact rest.1 y hy
    · simp only [List.map_cons,one.2.1,rest.2.1]

theorem fromFn {T C V : Type} (n : Usize) (f : core.ops.function.FnMut C Usize T)
    (P : T → Prop) (observe : T → V) (model : Nat → V)
    (c : C) (out : Array T n)
    (step : ∀ i : Usize,i.val<n.val → ∀ x c',f.call_mut c i=ok (x,c') →
      P x ∧ observe x=model i.val ∧ c'=c)
    (run : OraclePortStdBuilder.fromFn n f c=ok out) :
    (∀ x∈out.val,P x) ∧ out.val.map observe=List.ofFn (fun i : Fin n.val=>model i.val) := by
  unfold OraclePortStdBuilder.fromFn at run
  obtain ⟨⟨xs,last⟩,called,r1⟩ := FIv_Map.bind_success _ _ _ run
  have hstep : ∀ i∈OraclePortStdBuilder.indices n,∀ x c',f.call_mut c i=ok (x,c') →
      P x ∧ observe x=model i.val ∧ c'=c := by
    intro i hi
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hi
    subst i
    apply step
    exact j.isLt
  have values := loop f P observe (fun i=>model i.val) _ c xs last hstep called
  simp only at r1
  split at r1
  · have eq := congrArg Subtype.val (Result.ok.inj r1)
    rw [←eq]
    refine ⟨values.1,?_⟩
    rw [values.2.1]
    simp only [OraclePortStdBuilder.indices,List.map_ofFn,Function.comp_def]
    congr 1
  · cases r1
#print axioms loop
#print axioms fromFn
end AspisR1.FIx_Builder
end
