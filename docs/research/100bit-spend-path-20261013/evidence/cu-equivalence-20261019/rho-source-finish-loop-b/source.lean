import AspisR1CuRhoSource.Finish
import CuSavingsRhoSourceNext
import CuSavingsRhoFinishLoop

/-! Consume the extracted standard next theorem through the unchanged finish
loop. The backward observer is proved insensitive to the discarded counter;
the entire returned inner iterator, including its slice, is preserved. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoSourceFinishLoop
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1CuRho
open CuSavingsRhoFinishModel CuSavingsRhoFinishNext

def BackInvariant (back : Enum → Enum) : Prop :=
  ∀ a b, a.iter = b.iter → (back a).iter = (back b).iter

theorem loop_unroll (iter : Enum) (back : Enum → Enum) (self : verifier.BatchedWeights) :
    AspisR1CuRhoSource.verifier.BatchedWeights.finish_loop iter back self = (do
      let result ← AspisR1CuRhoSource.verifier.BatchedWeights.finish_loop.body self iter back
      match result with
      | .done out => .ok out
      | .cont (next,handback) =>
        AspisR1CuRhoSource.verifier.BatchedWeights.finish_loop next handback self) := by
  unfold AspisR1CuRhoSource.verifier.BatchedWeights.finish_loop
  rw [loop]
  simp only [Prod.casesOn]
  cases h : AspisR1CuRhoSource.verifier.BatchedWeights.finish_loop.body self iter back with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok result => cases result <;> simp only [h,bind_tc_ok] <;> rfl

theorem source_success_fuel (fuel : Nat) (iter : Enum) (back : Enum → Enum)
    (self : verifier.BatchedWeights)
    (hlen : iter.iter.slice.val.length = (canonicalSlice self).val.length)
    (hspan : iter.iter.i+fuel = iter.iter.slice.val.length)
    (hcount : iter.count.val = iter.iter.i) (hback : BackInvariant back) :
    ∃ last : Enum,
      AspisR1CuRhoSource.verifier.BatchedWeights.finish_loop iter back self = .ok last ∧
      last.iter = (back (modelIter iter (canonicalSlice self) hlen)).iter := by
  induction fuel generalizing iter back with
  | zero =>
    have hend : iter.iter.i = iter.iter.slice.val.length := by omega
    have hn := CuSavingsRhoSourceNext.next_done iter hend
    simp only [CuSavingsRhoSourceNext.selectedNext] at hn
    have hbody : AspisR1CuRhoSource.verifier.BatchedWeights.finish_loop.body self iter back =
        .ok (.done (back iter)) := by
      simp only [AspisR1CuRhoSource.verifier.BatchedWeights.finish_loop.body,hn,bind_tc_ok]
      rfl
    refine ⟨back iter,?_,?_⟩
    · rw [loop_unroll,hbody]
      rfl
    · rw [model_at_end iter (canonicalSlice self) hlen hend hcount]
  | succ fuel ih =>
    have hi : iter.iter.i < iter.iter.slice.val.length := by omega
    have hit : iter.iter.i < (canonicalSlice self).val.length := by omega
    let value := (canonicalSlice self).val[iter.iter.i]'hit
    obtain ⟨count,hc,hm⟩ := CuSavingsRhoFinishNext.next_step iter hi hcount
    let state : Enum := {iter := {iter.iter with i := iter.iter.i+1},count := count}
    have hm' : CuSavingsIteratorBridge.modelNext iter =
        .ok (some (iter.count,iter.iter.slice.val[iter.iter.i]'hi),state,handback iter.iter.i) := hm
    obtain ⟨sourceBack,hs,hproj⟩ := CuSavingsRhoSourceNext.from_model_success
      iter (iter.count,value) (some (iter.count,iter.iter.slice.val[iter.iter.i]'hi))
      state (handback iter.iter.i) hm'
    simp only [CuSavingsRhoSourceNext.selectedNext] at hs
    let newBack : Enum → Enum := fun out => back (sourceBack out (some (iter.count,value)))
    have hv := CuSavingsRhoFinishLoop.value_target self iter hlen hi hcount
    have hbody : AspisR1CuRhoSource.verifier.BatchedWeights.finish_loop.body self iter back =
        .ok (.cont (state,newBack)) := by
      simp only [AspisR1CuRhoSource.verifier.BatchedWeights.finish_loop.body,hs,bind_tc_ok]
      change (do
        let w ← verifier.BatchedWeights.value self iter.count
        Result.ok (ControlFlow.cont (state,fun out => back (sourceBack out (some (iter.count,w)))) :
          ControlFlow (Enum × (Enum → Enum)) Enum)) = _
      rw [hv]
      rfl
    have hnew : BackInvariant newBack := by
      intro a b hab
      change (back (sourceBack a (some (iter.count,value)))).iter =
        (back (sourceBack b (some (iter.count,value)))).iter
      apply hback
      rw [hproj a,hproj b]
      exact congrArg (fun it : Iter => {it with slice := it.slice.setAtNat iter.iter.i value}) hab
    have hspan' : state.iter.i+fuel = state.iter.slice.val.length := by
      change iter.iter.i+1+fuel = iter.iter.slice.val.length
      omega
    have hcount' : state.count.val = state.iter.i := hc
    obtain ⟨last,hrun,hiter⟩ := ih state newBack hlen hspan' hcount' hnew
    refine ⟨last,?_,?_⟩
    · rw [loop_unroll,hbody]
      exact hrun
    · have hmodel : handback iter.iter.i (modelIter state (canonicalSlice self) hlen)
          (some (iter.count,value)) = modelIter iter (canonicalSlice self) hlen := by
        simpa only [handback,state,value] using model_step iter (canonicalSlice self) hlen hit count
      calc
        last.iter = (newBack (modelIter state (canonicalSlice self) hlen)).iter := hiter
        _ = (back (handback iter.iter.i (modelIter state (canonicalSlice self) hlen)
            (some (iter.count,value)))).iter := hback _ _ (hproj _)
        _ = (back (modelIter iter (canonicalSlice self) hlen)).iter :=
          congrArg (fun out : Enum => (back out).iter) hmodel

theorem source_success (iter : Enum) (self : verifier.BatchedWeights)
    (hlen : iter.iter.slice.val.length = (canonicalSlice self).val.length)
    (hi : iter.iter.i ≤ iter.iter.slice.val.length)
    (hcount : iter.count.val = iter.iter.i) :
    ∃ last : Enum,
      AspisR1CuRhoSource.verifier.BatchedWeights.finish_loop iter (fun out => out) self = .ok last ∧
      last.iter = (modelIter iter (canonicalSlice self) hlen).iter := by
  exact source_success_fuel (iter.iter.slice.val.length-iter.iter.i) iter (fun out => out)
    self hlen (by omega) hcount (by intro a b hab;exact hab)

#print axioms loop_unroll
#print axioms source_success_fuel
#print axioms source_success
end AspisR1.CuSavingsRhoSourceFinishLoop
