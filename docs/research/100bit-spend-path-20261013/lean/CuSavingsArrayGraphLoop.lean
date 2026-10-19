import CuSavingsArrayGraphStep

/-! The entire emitted initialization loop equals a finite state-threading fill.
The only span premise discharges every source counter/index bound. Callback
failure and divergence are preserved, with no callback-success assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsArrayGraphLoop
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1CuArrayGraph CuSavingsArrayGraphStep

def fill {T F : Type} (inst : Aeneas.Std.core.ops.function.FnMut F Usize T) :
    Nat → F → Slice (Option T) → Usize → Result (Slice (Option T))
  | 0,_,buffer,_ => .ok buffer
  | n+1,state,buffer,i => do
      let (item,state1) ← inst.call_mut state i
      let next ← i + 1#usize
      fill inst n state1 (buffer.set i (some item)) next

abbrev sourceLoop {T F : Type} (inst : Aeneas.Std.core.ops.function.FnMut F Usize T) :=
  core.array.try_from_fn_erased_loop (CuSavingsTryGraphRuntime.neverTry T) inst

theorem loop_unroll {T F : Type} (inst : Aeneas.Std.core.ops.function.FnMut F Usize T)
    (back : Slice (Option T) → Slice (Option T)) (state : F)
    (buffer : Slice (Option T)) (i : Usize) :
    sourceLoop inst back state buffer i = (do
      let result ← core.array.try_from_fn_erased_loop.body
        (CuSavingsTryGraphRuntime.neverTry T) inst back state buffer i
      match result with
      | .done value => .ok value
      | .cont (back1,state1,buffer1,i1) => sourceLoop inst back1 state1 buffer1 i1) := by
  unfold sourceLoop core.array.try_from_fn_erased_loop
  rw [loop]
  simp only [Prod.casesOn]
  cases h : core.array.try_from_fn_erased_loop.body
      (CuSavingsTryGraphRuntime.neverTry T) inst back state buffer i with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok flow => cases flow <;> simp only [h,bind_tc_ok] <;> rfl

theorem source_eq_fill {T F : Type} (inst : Aeneas.Std.core.ops.function.FnMut F Usize T)
    (n : Nat) (back : Slice (Option T) → Slice (Option T)) (state : F)
    (buffer : Slice (Option T)) (i : Usize) (hspan : i.val+n = buffer.length) :
    sourceLoop inst back state buffer i = (do
      let final ← fill inst n state buffer i
      .ok (.Continue (),back final)) := by
  induction n generalizing state buffer i with
  | zero =>
    have hi : buffer.length ≤ i.val := by omega
    rw [loop_unroll,body_done inst back state buffer i hi]
    rfl
  | succ n ih =>
    have hi : i.val < buffer.length := by omega
    obtain ⟨next,hv,hbody⟩ := body_step inst back state buffer i hi
    obtain ⟨next1,hadd,hv1⟩ := CuSavingsArrayGuard.increment_success buffer i hi
    have heq : next1 = next := by scalar_tac
    subst next1
    rw [loop_unroll,hbody]
    simp only [fill,hadd]
    cases hcall : inst.call_mut state i with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨item,state1⟩
      simp only [bind_tc_ok]
      change sourceLoop inst back state1 (buffer.set i (some item)) next = (do
        let final ← (do
          let next2 ← UScalar.add i 1#usize
          fill inst n state1 (buffer.set i (some item)) next2)
        .ok (.Continue (),back final))
      rw [hadd]
      apply ih state1 (buffer.set i (some item)) next
      have hlen : (buffer.set i (some item)).length = buffer.length := Slice.set_length _ _ _
      rw [hlen,hv]
      omega

#print axioms fill
#print axioms loop_unroll
#print axioms source_eq_fill
end AspisR1.CuSavingsArrayGraphLoop
