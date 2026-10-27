import FIy_MapValue
set_option autoImplicit false
namespace AspisR1.FJa_MapRelation
open Aeneas Aeneas.Std Result
/-- Exact ordered input/output relation for the SAME traversal used by native
prepared-weight map; callback state must be retained, not chosen afresh. -/
theorem loop {A T C : Type} (f : C → A → Result (T × C)) (R : A → T → Prop)
    (is : List A) (c : C) (xs : List T) (last : C)
    (step : ∀ i∈is,∀ x c',f c i=ok (x,c') → R i x ∧ c'=c)
    (run : AspisV8R19.TraversalRuntime.mapState f is c=ok (xs,last)) :
    List.Forall₂ R is xs ∧ last=c := by
  induction is generalizing xs last with
  | nil =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)
    exact ⟨.nil,rfl⟩
  | cons i is ih =>
    unfold AspisV8R19.TraversalRuntime.mapState at run
    obtain ⟨⟨x,c'⟩,hhead,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨⟨ys,last'⟩,htail,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)
    have head := step i (by simp) x c' hhead
    have same := head.2
    subst c'
    have tail := ih ys last' (by intro i hi;exact step i (by simp [hi])) htail
    exact ⟨.cons head.1 tail.1,tail.2⟩
theorem value {A T C : Type} {N : Usize} (f : core.ops.function.FnMut C A T)
    (R : A → T → Prop) (a : Array A N) (c : C) (out : Array T N)
    (step : ∀ i∈a.val,∀ x c',f.call_mut c i=ok (x,c') → R i x ∧ c'=c)
    (run : Aeneas.Std.core.array.Array.map f a c=ok out) : List.Forall₂ R a.val out.val := by
  unfold Aeneas.Std.core.array.Array.map at run
  split at run
  · rename_i xs last called
    have v := loop f.call_mut R a.val c xs last step called
    have same := congrArg Subtype.val (Result.ok.inj run)
    rw [←same]
    exact v.1
  · cases run
  · cases run
#print axioms loop
#print axioms value
end AspisR1.FJa_MapRelation
