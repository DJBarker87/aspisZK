import AspisV8R19.TraversalRuntime

/-! Laws of the concrete traversal models. Not a theorem about arbitrary Rust
Iterator::try_fold overrides, pointer-level slices or panic destructors. -/
set_option autoImplicit false
namespace AspisV8R19.TraversalLaws
open Aeneas Aeneas.Std Result ControlFlow TraversalRuntime

theorem map_append {T U F : Type} (call : F → T → Result (U × F))
    (xs ys : List T) (state : F) :
    mapState call (xs++ys) state = (do
      let (left,middle) ← mapState call xs state
      let (right,last) ← mapState call ys middle
      .ok (left++right,last)) := by
  induction xs generalizing state with
  | nil => cases h : mapState call ys state <;> simp [mapState,h]
  | cons x xs ih =>
    simp only [List.cons_append,mapState,ih,bind_assoc_eq]
    cases hc : call state x with
    | fail e => simp
    | div => simp
    | ok pair =>
      rcases pair with ⟨value,middle⟩
      cases ht : mapState call xs middle with
      | fail e => simp [ht]
      | div => simp [ht]
      | ok pair =>
        rcases pair with ⟨tail,last⟩
        cases hr : mapState call ys last <;> simp [ht,hr]

theorem map_first_failure {T U F : Type} (call : F → T → Result (U × F))
    (x : T) (xs : List T) (state : F) (e : Error) (h : call state x = .fail e) :
    mapState call (x::xs) state = .fail e := by simp [mapState,h]

theorem map_first_divergence {T U F : Type} (call : F → T → Result (U × F))
    (x : T) (xs : List T) (state : F) (h : call state x = .div) :
    mapState call (x::xs) state = .div := by simp [mapState,h]

theorem map_pure {T U F : Type} (f : T → U) (xs : List T) (state : F) :
    mapState (fun s x => .ok (f x,s)) xs state = .ok (xs.map f,state) := by
  induction xs <;> simp [mapState, *]

theorem map_eta {T U F : Type} (call : F → T → Result (U × F)) (xs : List T) (state : F) :
    mapState (fun s x => call s x) xs state = mapState call xs state := rfl

theorem map_four {T U F : Type} (call : F → T → Result (U × F)) (a b c d : T) (state : F) :
    mapState call [a,b,c,d] state = (do
      let (a',s1) ← call state a
      let (b',s2) ← call s1 b
      let (c',s3) ← call s2 c
      let (d',s4) ← call s3 d
      .ok ([a',b',c',d'],s4)) := by
  simp only [mapState,bind_assoc_eq,bind_tc_ok]

theorem array_four {T U F : Type} (fn : core.ops.function.FnMut F T U)
    (a b c d : T) (a' b' c' d' : U) (s0 s1 s2 s3 s4 : F)
    (ha : fn.call_mut s0 a = .ok (a',s1)) (hb : fn.call_mut s1 b = .ok (b',s2))
    (hc : fn.call_mut s2 c = .ok (c',s3)) (hd : fn.call_mut s3 d = .ok (d',s4)) :
    core.array.Array.map fn (Array.make 4#usize [a,b,c,d]) s0 =
      .ok (Array.make 4#usize [a',b',c',d']) := by
  have hm : mapState fn.call_mut [a,b,c,d] s0 = .ok ([a',b',c',d'],s4) := by
    simp [map_four,ha,hb,hc,hd]
  unfold core.array.Array.map
  split
  · rename_i ys last he
    change mapState fn.call_mut [a,b,c,d] s0 = .ok (ys,last) at he
    rw [hm] at he
    cases Result.ok.inj he
    rfl
  · rename_i e he
    change mapState fn.call_mut [a,b,c,d] s0 = .fail e at he
    rw [hm] at he
    cases he
  · rename_i he
    change mapState fn.call_mut [a,b,c,d] s0 = .div at he
    rw [hm] at he
    cases he

theorem array_empty {T U F : Type} (fn : core.ops.function.FnMut F T U) (s : F) :
    core.array.Array.map fn (Array.make 0#usize []) s = .ok (Array.make 0#usize []) := by
  simp [core.array.Array.map,Array.make,mapState]

theorem stateful_map_control :
    mapState (fun (s x : Nat) => .ok (s+x,s+x)) [1,2,3] 0 = .ok ([1,3,6],6) := rfl

theorem stale_state_negative :
    mapState (fun (s x : Nat) => .ok (s+x,s+x)) [1,2,3] 0 ≠ .ok ([1,2,3],0) := by
  rw [stateful_map_control]
  intro h
  have h' := congrArg Prod.snd (Result.ok.inj h)
  contradiction

theorem any_done {I T F : Type} (next : I → Result (Option T × I))
    (call : F → T → Result (Bool × F)) (i j : I) (s : F)
    (h : next i = .ok (none,j)) : anyRun next call i s = .ok (false,j) := by
  rw [anyRun,loop.eq_def]
  simp only [anyBody,h,bind_tc_ok]

theorem any_hit {I T F : Type} (next : I → Result (Option T × I))
    (call : F → T → Result (Bool × F)) (i j : I) (s t : F) (x : T)
    (hn : next i = .ok (some x,j)) (hc : call s x = .ok (true,t)) :
    anyRun next call i s = .ok (true,j) := by
  rw [anyRun,loop.eq_def]
  simp only [anyBody,hn,hc,bind_tc_ok,if_true]

theorem any_continue {I T F : Type} (next : I → Result (Option T × I))
    (call : F → T → Result (Bool × F)) (i j : I) (s t : F) (x : T)
    (hn : next i = .ok (some x,j)) (hc : call s x = .ok (false,t)) :
    anyRun next call i s = anyRun next call j t := by
  rw [anyRun,loop.eq_def]
  simp only [anyBody,hn,hc,bind_tc_ok,Bool.false_eq_true,if_false]
  rfl

theorem any_next_failure {I T F : Type} (next : I → Result (Option T × I))
    (call : F → T → Result (Bool × F)) (i : I) (s : F) (e : Error)
    (h : next i = .fail e) : anyRun next call i s = .fail e := by
  rw [anyRun,loop.eq_def]
  simp only [anyBody,h,bind_tc_fail]

theorem any_callback_failure {I T F : Type} (next : I → Result (Option T × I))
    (call : F → T → Result (Bool × F)) (i j : I) (s : F) (x : T) (e : Error)
    (hn : next i = .ok (some x,j)) (hc : call s x = .fail e) :
    anyRun next call i s = .fail e := by
  rw [anyRun,loop.eq_def]
  simp only [anyBody,hn,hc,bind_tc_ok,bind_tc_fail]

theorem chain_left_hit {A B T : Type} (left : core.iter.traits.iterator.Iterator A T)
    (right : core.iter.traits.iterator.Iterator B T) (a a' : A) (b : Option B) (x : T)
    (h : left.next a = .ok (some x,a')) :
    core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator.next left right ⟨some a,b⟩ =
      .ok (some x,⟨some a',b⟩) := by
  simp [core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator.next,h]

theorem chain_left_exhausted {A B T : Type} (left : core.iter.traits.iterator.Iterator A T)
    (right : core.iter.traits.iterator.Iterator B T) (a a' : A) (b : Option B)
    (h : left.next a = .ok (none,a')) :
    core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator.next left right ⟨some a,b⟩ =
      core.iter.adapters.chain.rightNext right (⟨none,b⟩ : core.iter.adapters.chain.Chain A B) := by
  simp [core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator.next,h]

theorem chain_right_not_fused {A B T : Type} (right : core.iter.traits.iterator.Iterator B T)
    (a : Option A) (b b' : B) (h : right.next b = .ok (none,b')) :
    core.iter.adapters.chain.rightNext right (⟨a,some b⟩ : core.iter.adapters.chain.Chain A B) =
      .ok (none,⟨a,some b'⟩) := by
  simp [core.iter.adapters.chain.rightNext,h]

theorem option_some {T E : Type} (x : T) (e : E) :
    core.option.Option.ok_or (some x) e = .ok (.Ok x) := rfl

theorem option_none {T E : Type} (e : E) :
    core.option.Option.ok_or (none : Option T) e = .ok (.Err e) := rfl

#print axioms map_append
#print axioms map_first_failure
#print axioms map_first_divergence
#print axioms map_pure
#print axioms map_eta
#print axioms map_four
#print axioms array_four
#print axioms array_empty
#print axioms stateful_map_control
#print axioms stale_state_negative
#print axioms any_done
#print axioms any_hit
#print axioms any_continue
#print axioms any_next_failure
#print axioms any_callback_failure
#print axioms chain_left_hit
#print axioms chain_left_exhausted
#print axioms chain_right_not_fused
#print axioms option_some
#print axioms option_none
end AspisV8R19.TraversalLaws
