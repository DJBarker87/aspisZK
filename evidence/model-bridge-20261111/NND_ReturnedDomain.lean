import NND_PoolReturned
set_option autoImplicit false
namespace NND_Returned
open RSL
/-- The domain is recovered from the SAME admitted call observation. This
lemma adds no domain or child-endpoint hypothesis to the parent. -/
theorem call_domain {A B : Type} (dom : A → Prop) (law : A → Spec B) (a : A)
 (env : Env) (x : B) (h : dom a → Returns (law a) env x) :
 Returns (Spec.call dom law a) env x := by
 intro o r hc hr
 exact h hc.1 o r hc.2 hr

/-- Out-of-bounds indexing aborts. The error value here is arbitrary and is
never asserted to be a returning implementation outcome on that arm. -/
def indexValue {α : Type} (xs : List α) (i : Nat) : Except ProgramError α :=
 option xs[i]? .invalidArgument

theorem index {α : Type} (env : Env) (xs : List α) (i : Nat) :
 Returns (RS.index xs i) env (indexValue xs i) := by
 unfold RS.index indexValue
 cases h : xs[i]? with
 | some a => exact rs_pure env a
 | none =>
   unfold RS.lift Spec.map
   intro o r h hr
   rcases h with ⟨u,e1,o2,h1,h2,ho⟩ | ⟨e1,h1,ho⟩ | ⟨e1,h1,ho⟩
   · simp [Spec.panic] at h1
   · subst ho; cases hr
   · subst ho; cases hr

#print axioms call_domain
#print axioms index
end NND_Returned
