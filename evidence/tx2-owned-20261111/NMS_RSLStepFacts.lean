import NMS_RSLRefine
set_option autoImplicit false
namespace NMS_RSLStepFacts
open RSL NMS_RSLRefine

/-- Path-sensitive composition uses the first step's actual returned cut at
the SAME environment. No condition is required on an unexecuted suffix. -/
theorem rsbind_using {A B : Type} {m n : RS A} {k l : A → RS B}
 (first : Refines m n)
 (next : ∀ env a events, m env ⟨.ret (.ok a),events⟩ →
   ∀ o, k a env o → l a env o) :
 Refines (RS.bind m k) (RS.bind n l) := by
 intro env o h
 rcases h with ⟨reply,evs,o2,hm,hk,ho⟩ | ⟨evs,hm,ho⟩ | ⟨evs,hm,ho⟩
 · refine Or.inl ⟨reply,evs,o2,first env _ hm,?_,ho⟩
   cases reply with
   | ok a => exact next env a evs hm o2 hk
   | error e => exact hk
 · exact Or.inr (Or.inl ⟨evs,first env _ hm,ho⟩)
 · exact Or.inr (Or.inr ⟨evs,first env _ hm,ho⟩)

theorem check_return (bad : Bool) (error : ProgramError) (env : Env)
 (events : List Event) (run : RS.check bad error env ⟨.ret (.ok ()),events⟩) :
 bad = false := by
 cases bad with
 | false => rfl
 | true => have h := congrArg Obs.exit run; cases h

theorem ofOption_return {A : Type} (reply : Option A) (error : ProgramError)
 (env : Env) (a : A) (events : List Event)
 (run : RS.ofOption reply error env ⟨.ret (.ok a),events⟩) : reply = some a := by
 cases reply with
 | none => have h := congrArg Obs.exit run; cases h
 | some b =>
   have h := Except.ok.inj (Exit.ret.inj (congrArg Obs.exit run))
   exact congrArg some h.symm

theorem index_return {A : Type} (xs : List A) (index : Nat) (env : Env)
 (a : A) (events : List Event)
 (run : RS.index xs index env ⟨.ret (.ok a),events⟩) : xs[index]? = some a := by
 unfold RS.index at run
 cases found : xs[index]? with
 | some b =>
   simp only [found] at run
   have h := Except.ok.inj (Exit.ret.inj (congrArg Obs.exit run))
   exact congrArg some h.symm
 | none =>
   simp only [found] at run
   unfold RS.lift Spec.map at run
   rcases run with ⟨u,evs,o,hm,hk,ho⟩ | ⟨evs,hm,ho⟩ | ⟨evs,hm,ho⟩
   · cases hm
   · cases ho
   · cases ho

theorem lift {A : Type} {m n : Spec A} (h : Refines m n) :
 Refines (RS.lift m) (RS.lift n) := bind h (fun _ => refl _)

#print axioms rsbind_using
#print axioms check_return
#print axioms ofOption_return
#print axioms index_return
#print axioms lift
end NMS_RSLStepFacts
