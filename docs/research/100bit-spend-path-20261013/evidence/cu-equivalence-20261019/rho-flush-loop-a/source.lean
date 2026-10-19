import CuSavingsRhoFlushModel

/-! Full source flush-loop induction, including application of the returned
mutable-iterator handback. The postcondition is equality of complete iterator
states after handback, not just equality of the individually folded values. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoFlushLoop
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1CuRho
open AspisR1.CuSavingsRhoFlushModel

theorem loop_unroll (iter : Iter) (back : Iter → Iter) :
    verifier.BatchedWeights.push_loop1 iter back = (do
      let result ← verifier.BatchedWeights.push_loop1.body iter back
      match result with
      | .done out => .ok out
      | .cont (next,handback) => verifier.BatchedWeights.push_loop1 next handback) := by
  unfold verifier.BatchedWeights.push_loop1
  rw [loop]
  simp only [Prod.casesOn]
  cases h : verifier.BatchedWeights.push_loop1.body iter back with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok result => cases result <;> simp only [h,bind_tc_ok] <;> rfl

theorem source_success_fuel (fuel : Nat) (iter : Iter) (back : Iter → Iter)
    (hspan : iter.i+fuel = iter.slice.val.length) :
    ∃ (last : Iter) (handback : Iter → Iter),
      verifier.BatchedWeights.push_loop1 iter back = .ok (last,handback) ∧
      handback last = back (modelIter iter) := by
  induction fuel generalizing iter back with
  | zero =>
    have hend : iter.i = iter.slice.val.length := by omega
    have hnext : Aeneas.Std.core.slice.iter.IteratorIterMut.next iter =
        .ok (none,iter,fun out _ => out) := by
      unfold Aeneas.Std.core.slice.iter.IteratorIterMut.next
      split
      · rename_i hi;exact False.elim (by omega)
      · rfl
    have hbody : verifier.BatchedWeights.push_loop1.body iter back =
        .ok (.done (iter,back)) := by
      simp only [verifier.BatchedWeights.push_loop1.body,hnext,bind_tc_ok]
      rfl
    refine ⟨iter,back,?_,?_⟩
    · rw [loop_unroll,hbody]
      rfl
    · rw [model_at_end iter hend]
  | succ fuel ih =>
    have hi : iter.i < iter.slice.val.length := by omega
    let limb := iter.slice.val[iter.i]'hi
    let next : Iter := {iter with i := iter.i+1}
    let nextBack : Iter → Option U64 → Iter := fun out value =>
      match value with
      | none => out
      | some x => {out with slice := out.slice.setAtNat iter.i x}
    let newBack : Iter → Iter := fun out =>
      back {out with slice := out.slice.setAtNat iter.i (foldWord limb)}
    have hnext : Aeneas.Std.core.slice.iter.IteratorIterMut.next iter =
        .ok (some limb,next,nextBack) := by
      unfold Aeneas.Std.core.slice.iter.IteratorIterMut.next
      split
      · rfl
      · rename_i hbad;exact False.elim (hbad hi)
    have hbody : verifier.BatchedWeights.push_loop1.body iter back =
        .ok (.cont (next,newBack)) := by
      simpa only [nextBack,newBack] using source_body_step iter next back limb nextBack hnext
    have hspan' : next.i+fuel=next.slice.val.length := by
      change iter.i+1+fuel=iter.slice.val.length
      omega
    obtain ⟨last,handback,hrun,hmodel⟩ := ih next newBack hspan'
    refine ⟨last,handback,?_,?_⟩
    · rw [loop_unroll,hbody]
      exact hrun
    · change handback last = back
        {modelIter {iter with i := iter.i+1} with
          slice := (modelIter {iter with i := iter.i+1}).slice.setAtNat iter.i
            (foldWord (iter.slice.val[iter.i]'hi))} at hmodel
      rw [model_step iter hi] at hmodel
      exact hmodel

theorem source_success (iter : Iter) (hi : iter.i ≤ iter.slice.val.length) :
    ∃ (last : Iter) (handback : Iter → Iter),
      verifier.BatchedWeights.push_loop1 iter (fun out => out) = .ok (last,handback) ∧
      handback last = modelIter iter := by
  exact source_success_fuel (iter.slice.val.length-iter.i) iter (fun out => out) (by omega)

#print axioms loop_unroll
#print axioms source_success_fuel
#print axioms source_success
end AspisR1.CuSavingsRhoFlushLoop
