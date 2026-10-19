import CuSavingsRhoFinishNext

/-! Full emitted finish-loop execution under the local mutable-enumerate
interface. Every output slot is replaced by the checked canonical value.
Source admission of that interface and enclosing callers remain required. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoFinishLoop
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1CuRho
open AspisR1.CuSavingsRhoValue AspisR1.CuSavingsRhoFinishModel
open AspisR1.CuSavingsRhoFinishNext

theorem loop_unroll (iter : Enum) (back : Enum → Enum) (self : verifier.BatchedWeights) :
    verifier.BatchedWeights.finish_loop iter back self = (do
      let result ← verifier.BatchedWeights.finish_loop.body self iter back
      match result with
      | .done out => .ok out
      | .cont (next,handback) => verifier.BatchedWeights.finish_loop next handback self) := by
  unfold verifier.BatchedWeights.finish_loop
  rw [loop]
  simp only [Prod.casesOn]
  cases h : verifier.BatchedWeights.finish_loop.body self iter back with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok result => cases result <;> simp only [h,bind_tc_ok] <;> rfl

theorem value_target (self : verifier.BatchedWeights) (iter : Enum)
    (hlen : iter.iter.slice.val.length = (canonicalSlice self).val.length)
    (hi : iter.iter.i < iter.iter.slice.val.length)
    (hcount : iter.count.val = iter.iter.i) :
    verifier.BatchedWeights.value self iter.count =
      .ok ((canonicalSlice self).val[iter.iter.i]'(by omega)) := by
  have hraw : iter.count.val < self.raw.val.length := by
    simp only [canonicalSlice,List.length_map] at hlen
    omega
  obtain ⟨raw,hv,hr⟩ := value_success self iter.count hraw
  rw [hv]
  apply congrArg Result.ok
  rw [hr]
  simp only [canonicalSlice,List.getElem_map]
  simp only [hcount]

theorem source_success_fuel (fuel : Nat) (iter : Enum) (back : Enum → Enum)
    (self : verifier.BatchedWeights)
    (hlen : iter.iter.slice.val.length = (canonicalSlice self).val.length)
    (hspan : iter.iter.i+fuel = iter.iter.slice.val.length)
    (hcount : iter.count.val = iter.iter.i) :
    verifier.BatchedWeights.finish_loop iter back self =
      .ok (back (modelIter iter (canonicalSlice self) hlen)) := by
  induction fuel generalizing iter back with
  | zero =>
    have hend : iter.iter.i = iter.iter.slice.val.length := by omega
    have hn := next_done iter hend
    simp only [next] at hn
    have hbody : verifier.BatchedWeights.finish_loop.body self iter back =
        .ok (.done (back iter)) := by
      simp only [verifier.BatchedWeights.finish_loop.body,hn,bind_tc_ok]
      rfl
    rw [loop_unroll,hbody]
    simp only [bind_tc_ok,model_at_end iter (canonicalSlice self) hlen hend hcount]
  | succ fuel ih =>
    have hi : iter.iter.i < iter.iter.slice.val.length := by omega
    have hit : iter.iter.i < (canonicalSlice self).val.length := by omega
    obtain ⟨count,hc,hn⟩ := next_step iter hi hcount
    simp only [next] at hn
    let state : Enum := {iter := {iter.iter with i := iter.iter.i+1},count := count}
    let newBack : Enum → Enum := fun out =>
      back {out with iter := {out.iter with slice := out.iter.slice.setAtNat iter.iter.i ((canonicalSlice self).val[iter.iter.i]'hit)}}
    have hv := value_target self iter hlen hi hcount
    have hbody : verifier.BatchedWeights.finish_loop.body self iter back =
        .ok (.cont (state,newBack)) := by
      simp only [verifier.BatchedWeights.finish_loop.body,hn,bind_tc_ok]
      dsimp only
      rw [hv]
      rfl
    have hspan' : state.iter.i+fuel = state.iter.slice.val.length := by
      change iter.iter.i+1+fuel = iter.iter.slice.val.length
      omega
    have hcount' : state.count.val = state.iter.i := hc
    have hr := ih state newBack hlen hspan' hcount'
    rw [loop_unroll,hbody]
    change verifier.BatchedWeights.finish_loop state newBack self = _
    rw [hr]
    apply congrArg Result.ok
    change back {modelIter state (canonicalSlice self) hlen with
      iter := {(modelIter state (canonicalSlice self) hlen).iter with
        slice := (modelIter state (canonicalSlice self) hlen).iter.slice.setAtNat
          iter.iter.i ((canonicalSlice self).val[iter.iter.i]'hit)}} = _
    rw [model_step iter (canonicalSlice self) hlen hit count]

theorem source_success (iter : Enum) (self : verifier.BatchedWeights)
    (hlen : iter.iter.slice.val.length = (canonicalSlice self).val.length)
    (hi : iter.iter.i ≤ iter.iter.slice.val.length)
    (hcount : iter.count.val = iter.iter.i) :
    verifier.BatchedWeights.finish_loop iter (fun out => out) self =
      .ok (modelIter iter (canonicalSlice self) hlen) := by
  exact source_success_fuel (iter.iter.slice.val.length-iter.iter.i) iter (fun out => out)
    self hlen (by omega) hcount

#print axioms loop_unroll
#print axioms value_target
#print axioms source_success_fuel
#print axioms source_success
end AspisR1.CuSavingsRhoFinishLoop
