import CuSavingsLibraSourceHandback

/-! Source scalar/array control and finite-loop induction shared by both
complete emitted Libra helpers. Arithmetic is not interpreted here. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1.CuSavingsLibraSourceControl

def lookup {T : Type} {N : Usize} (array : Array T N) (default : T) (i : Nat) : T :=
  array.val.getD i default

theorem read {T : Type} {N : Usize} (array : Array T N) (default : T)
    (i : Usize) (hi : i.val<N.val) :
    Array.index_usize array i = .ok (lookup array default i.val) := by
  have hlen : i.val<array.val.length := by simpa only [array.property] using hi
  obtain ⟨out,hr,hv⟩ := WP.spec_imp_exists (Array.index_usize_spec array i hlen)
  have he : out=lookup array default i.val :=
    hv.trans (List.getD_eq_getElem array.val default hlen).symm
  simpa only [he] using hr

def execute {S A : Type} (body : S → Result (ControlFlow S A)) (state : S) : Result A :=
  loop body state

theorem execute_unroll {S A : Type} (body : S → Result (ControlFlow S A)) (state : S) :
    execute body state = (do
      let step ← body state
      match step with
      | .done value => .ok value
      | .cont next => execute body next) := by
  unfold execute
  rw [loop]
  cases h : body state with
  | fail e => rfl
  | div => rfl
  | ok flow => cases flow <;> rfl

/-- A successful source loop body can be accumulated symbolically without
normalizing the fixpoint or exposing the arithmetic internals. -/
theorem execute_success {S A : Type} (body : S → Result (ControlFlow S A))
    (states : Nat → S) (value : A) (n : Nat)
    (step : ∀ i, i<n → body (states i)=.ok (.cont (states (i+1))))
    (done : body (states n)=.ok (.done value)) :
    execute body (states 0)=.ok value := by
  have go : ∀ fuel start, start+fuel=n → execute body (states start)=.ok value := by
    intro fuel
    induction fuel with
    | zero =>
      intro start hs
      have he : start=n := by omega
      rw [he,execute_unroll,done]
      rfl
    | succ fuel ih =>
      intro start hs
      have hi : start<n := by omega
      rw [execute_unroll,step start hi]
      simp only [bind_tc_ok]
      exact ih (start+1) (by omega)
  exact go n 0 (by omega)

/-- A finite source loop with an invariant yields an actual successful result.
No loop-success premise is assumed; each source step and termination branch
must be derived by its caller. -/
theorem execute_invariant {S A : Type} (body : S → Result (ControlFlow S A))
    (counter : S → Nat) (I : S → Prop) (Q : A → Prop) (bound : Nat)
    (step : ∀ state, I state → counter state<bound →
      ∃ next, body state=.ok (.cont next) ∧ I next ∧ counter next=counter state+1)
    (done : ∀ state, I state → counter state=bound →
      ∃ value, body state=.ok (.done value) ∧ Q value)
    (state : S) (hI : I state) (hb : counter state≤bound) :
    ∃ value, execute body state=.ok value ∧ Q value := by
  have go : ∀ fuel state, I state → counter state+fuel=bound →
      ∃ value, execute body state=.ok value ∧ Q value := by
    intro fuel
    induction fuel with
    | zero =>
      intro state hI hs
      obtain ⟨value,hd,hq⟩ := done state hI (by omega)
      refine ⟨value,?_,hq⟩
      rw [execute_unroll,hd]
      rfl
    | succ fuel ih =>
      intro state hI hs
      obtain ⟨next,hn,hIn,hcount⟩ := step state hI (by omega)
      obtain ⟨value,hvalue,hq⟩ := ih next hIn (by omega)
      refine ⟨value,?_,hq⟩
      rw [execute_unroll,hn]
      simpa only [bind_tc_ok] using hvalue
  exact go (bound-counter state) state hI (by omega)

#print axioms execute_invariant
#print axioms read
#print axioms execute_unroll
#print axioms execute_success
end AspisR1.CuSavingsLibraSourceControl
