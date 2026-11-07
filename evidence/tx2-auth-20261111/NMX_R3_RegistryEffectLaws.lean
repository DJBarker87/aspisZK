import NMX_R3_RegistryEffects
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryEffectLaws
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects

theorem pure_right {A : Type} (m : RSL.Spec A) : RSL.Spec.bind m RSL.Spec.pure = m := by
 funext env o
 apply propext
 constructor
 · intro h
   rcases h with ⟨a,es,tail,hm,ht,ho⟩ | ⟨es,hm,ho⟩ | ⟨es,hm,ho⟩
   · subst tail
     subst o
     simpa only [List.append_nil] using hm
   · subst o; exact hm
   · subst o; exact hm
 · intro h
   rcases o with ⟨exit,es⟩
   cases exit with
   | ret a => exact Or.inl ⟨a,es,⟨.ret a,[]⟩,h,rfl,by simp only [List.append_nil]⟩
   | abort => exact Or.inr (Or.inl ⟨es,h,rfl⟩)
   | diverge => exact Or.inr (Or.inr ⟨es,h,rfl⟩)

theorem eval_call {A : Type} (c : Command A) : eval (call c) = commandSpec c := by
 change RSL.Spec.bind (commandSpec c) RSL.Spec.pure = commandSpec c
 exact pure_right _

theorem eval_scalar {A : Type} (r : Result A) : eval (scalar r) = scalarSpec r := eval_call _
theorem eval_data (a : r1_pool_adapter.owned.OwnedAccount) : eval (data a) = dataSpec a := eval_call _
theorem eval_pda (s : Slice (Slice U8)) (p : solana_pubkey.Pubkey) : eval (pda s p) = pdaSpec s p := eval_call _
theorem eval_pure {A : Type} (a : A) : eval (pure a : Program A) = RSL.Spec.pure a := rfl

theorem eval_if {A : Type} (p : Prop) [Decidable p] (a b : Program A) :
 eval (if p then a else b) = if p then eval a else eval b := by
 by_cases h : p <;> simp only [h,↓reduceIte]

theorem eval_control {A B C : Type} (cf : core.ops.control_flow.ControlFlow B C)
 (yes : C → Program A) (no : B → Program A) : eval (control cf yes no) =
 (match cf with | .Continue x => eval (yes x) | .Break e => eval (no e)) := by
 cases cf <;> rfl

theorem map_bind {A B C : Type} (f : B → C) (m : RSL.Spec A) (k : A → RSL.Spec B) :
 RSL.Spec.map f (RSL.Spec.bind m k) = RSL.Spec.bind m (fun a => RSL.Spec.map f (k a)) :=
 NMX_R2_SpecAssociativity.bind _ _ _

theorem map_pure {A B : Type} (f : A → B) (a : A) :
 RSL.Spec.map f (RSL.Spec.pure a) = RSL.Spec.pure (f a) := RSL.Spec.bind_pure _ _

#print axioms pure_right
#print axioms eval_call
#print axioms eval_scalar
#print axioms eval_data
#print axioms eval_pda
#print axioms eval_pure
#print axioms eval_if
#print axioms eval_control
#print axioms map_bind
#print axioms map_pure
end NMX_R3_RegistryEffectLaws
end
