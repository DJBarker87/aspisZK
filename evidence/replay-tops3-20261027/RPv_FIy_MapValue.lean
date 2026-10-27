import RPv_FIx_Builder
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_MapValue
open Aeneas Aeneas.Std Result
theorem loop {T C V A : Type} (f : C → A → Result (T × C))
    (P : T → Prop) (observe : T → V) (model : A → V)
    (is : List A) (c : C) (xs : List T) (last : C)
    (step : ∀ i∈is,∀ x c',f c i=ok (x,c') → P x ∧ observe x=model i ∧ c'=c)
    (run : AspisV8R19.TraversalRuntime.mapState f is c=ok (xs,last)) :
    (∀ x∈xs,P x) ∧ xs.map observe=is.map model ∧ last=c := by
  induction is generalizing xs last with
  | nil =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)
    exact ⟨by simp,rfl,rfl⟩
  | cons i is ih =>
    unfold AspisV8R19.TraversalRuntime.mapState at run
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

theorem value {T C V A : Type} {N : Usize} (f : core.ops.function.FnMut C A T)
    (P : T → Prop) (observe : T → V) (model : A → V) (a : Array A N) (c : C) (out : Array T N)
    (step : ∀ x∈a.val,∀ y c',f.call_mut c x=ok (y,c') → P y ∧ observe y=model x ∧ c'=c)
    (run : Aeneas.Std.core.array.Array.map f a c=ok out) :
    (∀ y∈out.val,P y) ∧ out.val.map observe=a.val.map model := by
  unfold Aeneas.Std.core.array.Array.map at run
  split at run
  · rename_i ys last called
    have v := loop f.call_mut P observe model a.val c ys last step called
    have eq := congrArg Subtype.val (Result.ok.inj run)
    rw [←eq]
    exact ⟨v.1,v.2.1⟩
  · cases run
  · cases run
#print axioms loop
#print axioms value
end AspisR1.FIy_MapValue
end
