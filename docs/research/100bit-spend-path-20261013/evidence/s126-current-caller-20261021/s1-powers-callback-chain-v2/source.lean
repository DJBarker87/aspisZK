import CurrentPowersExactProduct
set_option autoImplicit false
namespace AspisS1PowersCallbackChain
open Aeneas Aeneas.Std Result
open AspisR1PowersConcreteMul AspisR1PowersExactProduct
abbrev E := CallbackWide
abbrev Callback := E × E

/-- Iterate the complete emitted mutable callback, retaining its final state.
This is the callback chain, not a replacement for Std array::from_fn. -/
def execute (N : Usize) (state : Callback) : List Usize → Result (List E × Callback)
  | [] => ok ([],state)
  | i::indices => do
    let (value,next) ←
      AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
        sourceMul (N:=N) state i
    let (values,last) ← execute N next indices
    ok (value::values,last)

/-- TOTAL for every callback index list and canonical initial state. It
executes the last multiply and keeps its result; no per-step totality or
successful-child premise is assumed. All field carriers are complete. -/
theorem total_exact (N : Usize) (indices : List Usize) (p x : E)
    (hp : Canonical p) (hx : Canonical x) :
    ∃ values last,
      execute N (p,x) indices=ok (values,(last,x)) ∧
      values.length=indices.length ∧ Canonical last ∧
      decode last=decode p*decode x^indices.length ∧
      ∀ j, (hj : j<values.length) →
        Canonical (values[j]'hj) ∧ decode (values[j]'hj)=decode p*decode x^j := by
  induction indices generalizing p with
  | nil =>
    refine ⟨[],p,rfl,rfl,hp,?_,?_⟩
    · simp only [List.length_nil,pow_zero,mul_one]
    · intro j hj
      exact (Nat.not_lt_zero _ hj).elim
  | cons i indices ih =>
    obtain ⟨next,hnext,hproduct,hcall⟩ := powers_callback_total_exact (N:=N) p x hp hx i
    obtain ⟨values,last,hrun,hlen,hlast,hlastProduct,hcells⟩ := ih next hnext
    refine ⟨p::values,last,?_,?_,hlast,?_,?_⟩
    · simp only [execute,hcall,bind_tc_ok]
      dsimp only
      rw [hrun]
      rfl
    · simp only [List.length_cons,hlen]
    · rw [hlastProduct,hproduct,List.length_cons,pow_succ]
      ring
    · intro j hj
      cases j with
      | zero => simpa only [List.getElem_cons_zero,pow_zero,mul_one] using And.intro hp rfl
      | succ j =>
        have hlt : j<values.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hj
        obtain ⟨hc,he⟩ := hcells j hlt
        refine ⟨hc,?_⟩
        change decode (values[j]'hlt)=_
        rw [he,hproduct,pow_succ]
        ring

#print axioms execute
#print axioms total_exact
end AspisS1PowersCallbackChain
