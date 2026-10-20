import CuSavingsGeometryCandidate7
import CuSavingsGeometryCounter
set_option autoImplicit false
namespace AspisR1.CuSavingsGeometryStage
open Aeneas Aeneas.Std Result ControlFlow AspisR1GeometryCandidate7
open CuSavingsGeometryCandidate7 CuSavingsGeometryCaller CuSavingsGeometryFront
abbrev M := field.M31
abbrev State (P : Type) := Usize × P
abbrev Output (P : Type) := core.result.Result (State P) verifier.Error

private theorem bind_ok {A B : Type} (m : Result A) (k : A→Result B) (out : B)
    (h : (m >>= k)=.ok out) : ∃ value,m=.ok value ∧ k value=.ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok value => exact ⟨value,rfl,h⟩

/-- Exact source counter-field fission: unchanged coefficient/rhs/power work,
checked next+=1, then the unchanged query observer. Other fields are opaque. -/
def suffix {P A : Type} (index : Usize) (work : M→A→Result P)
    (mark : Usize→Result Unit) (node : M) (value : A) : Result (Output P) := do
  let payload ← work node value
  let next ← index+1#usize
  mark index
  .ok (.Ok (next,payload))

def oldQuery {P A : Type} (queries : Queries) (folds : Usize)
    (before : State P→Result (core.result.Result A verifier.Error))
    (work : State P→M→A→Result P) (mark : Usize→Result Unit)
    (state : State P) : Result (Output P) :=
  referenceQuery queries folds state.1 (before state) (suffix state.1 (work state) mark)
    (fun error=>.ok (.Err error))

def newQuery {P A : Type} (queries : Queries) (folds start : Usize)
    (cache : alloc.vec.Vec M) (before : State P→Result (core.result.Result A verifier.Error))
    (work : State P→M→A→Result P) (mark : Usize→Result Unit)
    (state : State P) : Result (Output P) :=
  optimizedQuery queries folds state.1 start cache (before state) (suffix state.1 (work state) mark)
    (fun error=>.ok (.Err error))

theorem suffix_next {P A : Type} (index : Usize) (work : M→A→Result P)
    (mark : Usize→Result Unit) (node : M) (value : A) (out : State P)
    (hi : index.val<22) (h : suffix index work mark node value=.ok (.Ok out)) :
    out.1.val=index.val+1 := by
  unfold suffix at h
  obtain ⟨payload,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨next,hnext,h⟩ := bind_ok _ _ _ h
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  have heq := core.result.Result.Ok.inj (Result.ok.inj h)
  have hout : next=out.1 := congrArg Prod.fst heq
  obtain ⟨expected,hs,hv⟩ := CuSavingsRhoPowerTail.next_success index hi
  have hn : next=expected := Result.ok.inj (hnext.symm.trans hs)
  rw [←hout,hn]
  exact hv

theorem query_next {P A : Type} (queries : Queries) (folds : Usize)
    (before : State P→Result (core.result.Result A verifier.Error))
    (work : State P→M→A→Result P) (mark : Usize→Result Unit) (state out : State P)
    (hi : state.1.val<22) (h : oldQuery queries folds before work mark state=.ok (.Ok out)) :
    out.1.val=state.1.val+1 := by
  unfold oldQuery referenceQuery at h
  obtain ⟨query,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨u,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨r,_,h⟩ := bind_ok _ _ _ h
  cases r with
  | Err e => cases h
  | Ok value =>
    obtain ⟨node,_,h⟩ := bind_ok _ _ _ h
    exact suffix_next state.1 (work state) mark node value out hi h

def body {P : Type} (finish : Usize) (query : State P→Result (Output P))
    (state : State P) : Result (ControlFlow (State P) (Output P)) := do
  if state.1<finish then
    let result ← query state
    match result with
    | .Err error => .ok (.done (.Err error))
    | .Ok next => .ok (.cont next)
  else .ok (.done (.Ok state))

def run {P : Type} (finish : Usize) (query : State P→Result (Output P))
    (state : State P) : Result (Output P) := loop (body finish query) state

theorem unroll {P : Type} (finish : Usize) (query : State P→Result (Output P)) (state : State P) :
    run finish query state=(do
      let flow ← body finish query state
      match flow with | .done out=>.ok out | .cont next=>run finish query next) := by
  unfold run
  rw [loop]
  cases h : body finish query state with
  | fail e => rfl
  | div => rfl
  | ok flow => cases flow <;> rfl

/-- Every loop call obtains its range certificate internally from successful
source counter advances, rather than assuming arbitrary cache indices valid. -/
theorem loop_equivalence {P A : Type} (queries : Queries) (folds start finish : Usize)
    (front : new.Front) (built : new.front queries start finish=.ok (.Ok front))
    (before : State P→Result (core.result.Result A verifier.Error))
    (work : State P→M→A→Result P) (mark : Usize→Result Unit)
    (fuel : Nat) (state : State P) (calls : Calls start state.1)
    (span : finish.val-state.1.val=fuel) :
    run finish (newQuery queries folds start front.line_z_values before work mark) state=
      run finish (oldQuery queries folds before work mark) state := by
  have hend := (CuSavingsGeometryCache.source_success queries start finish front built).2.1
  induction fuel generalizing state with
  | zero =>
    have hstop : ¬state.1<finish := by change ¬state.1.val<finish.val;omega
    rw [unroll,unroll]
    simp only [body,hstop,if_false,bind_tc_ok]
  | succ fuel ih =>
    have guard : state.1<finish := by change state.1.val<finish.val;omega
    have hi : state.1.val<22 := by change state.1.val<finish.val at guard;omega
    have heq : newQuery queries folds start front.line_z_values before work mark state=
        oldQuery queries folds before work mark state :=
      source_query_context queries folds state.1 start finish front built calls guard
        (before state) (suffix state.1 (work state) mark) (fun error=>.ok (.Err error))
    rw [unroll,unroll]
    simp only [body,guard,if_pos,heq,bind_assoc_eq]
    apply (bind_eq_iff (oldQuery queries folds before work mark state) _ _).mpr
    intro result hresult
    cases result with
    | Err e => rfl
    | Ok next =>
      have hn := query_next queries folds before work mark state next hi hresult
      exact ih next (Calls.advance calls hn) (by omega)

/-- Complete source loop from its actual initial next=start; no reachability,
cache-lineage, canonicality or candidate-equivalence hypothesis is supplied. -/
theorem source_loop_equivalence {P A : Type} (queries : Queries) (folds start finish : Usize)
    (front : new.Front) (built : new.front queries start finish=.ok (.Ok front))
    (before : State P→Result (core.result.Result A verifier.Error))
    (work : State P→M→A→Result P) (mark : Usize→Result Unit) (payload : P) :
    run finish (newQuery queries folds start front.line_z_values before work mark) (start,payload)=
      run finish (oldQuery queries folds before work mark) (start,payload) :=
  loop_equivalence queries folds start finish front built before work mark
    (finish.val-start.val) (start,payload) Calls.initial rfl

#print axioms suffix_next
#print axioms query_next
#print axioms loop_equivalence
#print axioms source_loop_equivalence
end AspisR1.CuSavingsGeometryStage
