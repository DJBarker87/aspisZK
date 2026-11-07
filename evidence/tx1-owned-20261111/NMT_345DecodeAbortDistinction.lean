import NMT_RSL_TX1_345
set_option autoImplicit false
namespace NMT_345DecodeAbortDistinction
open RSL
/-- A reached internal allocation followed by a rejecting decoder branch.
This is semantic distinction evidence, not an assertion of a native execution. -/
def allocationThenReject : RS Unit :=
 RS.seq (RS.lift Spec.alloc) (RS.throw .invalidAccountData)

theorem reached_allocation_abort (env : Env) :
 allocationThenReject env ⟨.abort,[]⟩ :=
 Or.inr (Or.inl ⟨[],Or.inr (Or.inl ⟨[],Or.inr rfl,rfl⟩),rfl⟩)

theorem option_none_no_abort {S : Type} (next : S → RS Unit) (env : Env) :
 ¬ RS.bind (RS.ofOption (none : Option S) .invalidAccountData) next env ⟨.abort,[]⟩ := by
 change ¬ RS.bind (RS.throw .invalidAccountData) next env ⟨.abort,[]⟩
 rw [RS.bind_throw]
 simp [RS.throw,Spec.pure]

theorem reject_models_differ {S : Type} (next : S → RS Unit) :
 allocationThenReject ≠ RS.bind (RS.ofOption (none : Option S) .invalidAccountData) next := by
 intro same
 have abort := reached_allocation_abort env0
 rw [same] at abort
 exact option_none_no_abort next env0 abort
#print axioms reached_allocation_abort
#print axioms option_none_no_abort
#print axioms reject_models_differ
end NMT_345DecodeAbortDistinction
