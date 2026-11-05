import NGL_DistinctStep
set_option autoImplicit false
noncomputable section
namespace NGL_DistinctInduction
open Aeneas Aeneas.Std Result ControlFlow
attribute [local instance] Classical.propDecidable
abbrev Account := NGL_DistinctStep.Account
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Reply := Option (core.result.Result Unit PE)
def keyAt {N : Usize} (a : Array Account N) (i : Usize) := (a.val[i.val]?).map (fun x => x.key)
def inner {N : Usize} (a : Array Account N) (index : Usize) : Nat → Usize → Result Reply
 | 0, _ => ok none
 | n+1, previous => if keyAt a previous = keyAt a index then
     ok (some (.Err .InvalidArgument)) else inner a index n (Usize.wrapping_add previous 1#usize)

theorem inner_source {N : Usize} (ops : AdapterRw.Ops) (a : Array Account N)
    (small : N.val ≤ 7) (index : Usize) (inside : index.val < a.val.length)
    (n : Nat) (previous : Usize) (left : previous.val+n=index.val) :
    AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
      (NGL_ReadonlyModel.install ops) a index previous = inner a index n previous := by
  induction n generalizing previous with
  | zero =>
    have outside : ¬ previous < index := by change ¬ previous.val < index.val; omega
    unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
    simp only [AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body,
      if_neg outside,inner]
  | succ n ih =>
    have before : previous.val < index.val := by omega
    have prevInside : previous.val < a.val.length := by omega
    have inc : (Usize.wrapping_add previous 1#usize).val = previous.val+1 :=
      NFQ_ZeroPrimitives.wrap_add previous 1#usize (by change previous.val+1≤4096; rw [a.property] at inside; omega)
    have rest := ih (Usize.wrapping_add previous 1#usize) (by rw [inc]; omega)
    have keys : keyAt a previous = keyAt a index ↔
        a.val[previous.val].key = a.val[index.val].key := by
      simp only [keyAt,List.getElem?_eq_getElem prevInside,List.getElem?_eq_getElem inside,
        Option.map_some,Option.some.injEq]
    unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
    rw [Aeneas.Std.loop.eq_def,NGL_DistinctStep.step ops a index previous inside before]
    by_cases same : a.val[previous.val].key = a.val[index.val].key
    · simp only [if_pos same,inner,if_pos (keys.mpr same)]
    · simp only [if_neg same,inner,if_neg (fun h => same (keys.mp h))]
      exact rest

def outer {N : Usize} (a : Array Account N) : Nat → Usize → Result Reply
 | 0, _ => ok none
 | n+1, index => do
   let pending ← inner a index index.val 0#usize
   match pending with
   | none => outer a n (Usize.wrapping_add index 1#usize)
   | some r => ok (some r)

theorem outer_source {N : Usize} (ops : AdapterRw.Ops) (a : Array Account N)
    (small : N.val ≤ 7) (n : Nat) (index : Usize) (left : index.val+n=N.val) :
    AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0
      (NGL_ReadonlyModel.install ops) a index = outer a n index := by
  induction n generalizing index with
  | zero =>
    have outside : ¬ index < N := by change ¬ index.val < N.val; omega
    unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0
    rw [Aeneas.Std.loop.eq_def]
    simp only [AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0.body,
      if_neg outside,outer]
  | succ n ih =>
    have inside : index.val < a.val.length := by rw [a.property]; omega
    have inc : (Usize.wrapping_add index 1#usize).val=index.val+1 :=
      NFQ_ZeroPrimitives.wrap_add index 1#usize (by change index.val+1≤4096; omega)
    have rest := ih (Usize.wrapping_add index 1#usize) (by rw [inc]; omega)
    have call := inner_source ops a small index inside index.val 0#usize
      (by change 0+index.val=index.val; omega)
    unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0
    rw [Aeneas.Std.loop.eq_def]
    simp only [AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0.body,
      if_pos (show index < N from (by change index.val < N.val; omega)),call,outer]
    cases value : inner a index index.val 0#usize with
    | fail err => simp only [value,bind_tc_fail]
    | div => simp only [value,bind_tc_div]
    | ok pending =>
      cases pending with
      | some r => simp only [value,bind_tc_ok]
      | none =>
        simp only [value,bind_tc_ok,lift]
        exact rest

def reference {N : Usize} (a : Array Account N) : Result (core.result.Result Unit PE) := do
  let pending ← outer a N.val 0#usize
  match pending with | none => ok (.Ok ()) | some r => ok r

theorem source {N : Usize} (ops : AdapterRw.Ops) (a : Array Account N) (small : N.val≤7) :
    AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
      (NGL_ReadonlyModel.install ops) a = reference a := by
  unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
  rw [outer_source ops a small N.val 0#usize (by change 0+N.val=N.val; omega)]
  rfl
#print axioms inner_source
#print axioms outer_source
#print axioms source
end NGL_DistinctInduction
