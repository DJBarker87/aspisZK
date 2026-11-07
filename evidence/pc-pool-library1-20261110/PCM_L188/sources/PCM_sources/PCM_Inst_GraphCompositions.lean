import PCM_Semantics
set_option autoImplicit false
namespace PCM_Inst_GraphCompositions
open PCM
/-- Installation always fixes the complete deterministic model. The domain is
that of the CLOSED child at these same arguments; it cannot be chosen later. -/
def install {A B : Type} (domain : A → Prop)
    (model : A → State → RSL.Env → Observation B) : Child A B :=
  ⟨domain, Graph domain model⟩

theorem call_exact {A B : Type} (domain : A → Prop)
    (model : A → State → RSL.Env → Observation B) (a : A)
    (s : State) (env : RSL.Env) (o : Observation B) :
    (install domain model).call a s env o ↔ domain a ∧ o = model a s env := by
  simp only [install,Child.call,Graph,and_self_left]

theorem caller_domain {A B : Type} (domain : A → Prop)
    (model : A → State → RSL.Env → Observation B) (a : A)
    (s : State) (env : RSL.Env) (o : Observation B)
    (h : (install domain model).call a s env o) : domain a :=
  ((call_exact domain model a s env o).mp h).1

theorem unique_on_domain {A B : Type} (domain : A → Prop)
    (model : A → State → RSL.Env → Observation B) (a : A)
    (s : State) (env : RSL.Env) (hd : domain a) :
    ∃! o, (install domain model).call a s env o := by
  refine ⟨model a s env,(call_exact _ _ _ _ _ _).mpr ⟨hd,rfl⟩,?_⟩
  intro o h
  exact ((call_exact _ _ _ _ _ _).mp h).2

/-- A representation adapter must prove the complete observation equation,
including all error and stop-prefix arms, at the SAME native occurrence.
No partial Result projection or returned-success witness suffices. -/
theorem transport {NativeArg NativeOut A B : Type}
    (args : NativeArg → A) (observe : NativeOut → Observation B)
    (nativeModel : NativeArg → NativeOut)
    (domain : A → Prop) (model : A → State → RSL.Env → Observation B)
    (a : NativeArg) (out : NativeOut) (s : State) (env : RSL.Env)
    (hd : domain (args a)) (native : out = nativeModel a)
    (adapter : observe (nativeModel a) = model (args a) s env) :
    (install domain model).call (args a) s env (observe out) := by
  apply (call_exact _ _ _ _ _ _).mpr
  exact ⟨hd,(congrArg observe native).trans adapter⟩
#print axioms call_exact
#print axioms caller_domain
#print axioms unique_on_domain
#print axioms transport
end PCM_Inst_GraphCompositions
