import WAdm_ArrayHelpers
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1.WAdm_WeightsHelpers
open WAdm_Fissioned WAdm_model WAdm_EmittedScalars

def sourceStep (state : alloc.vec.into_iter.IntoIter K × alloc.vec.Vec U8) :
    Result (ControlFlow (alloc.vec.into_iter.IntoIter K × alloc.vec.Vec U8) (alloc.vec.Vec U8)) :=
  WAdm_weights_loop.body state.1 state.2

theorem loop_normalize (iter : alloc.vec.into_iter.IntoIter K) (out : alloc.vec.Vec U8) :
    WAdm_weights_loop iter out = Aeneas.Std.loop sourceStep (iter,out) := by
  unfold WAdm_weights_loop
  apply congrArg (fun body => Aeneas.Std.loop body (iter,out))
  funext state
  rcases state with ⟨i,v⟩
  rfl

theorem loop_step (iter next : alloc.vec.into_iter.IntoIter K)
    (out mid after : alloc.vec.Vec U8)
    (step : WAdm_weights_loop.body iter out = ok (cont (next,mid)))
    (tail : WAdm_weights_loop next mid = ok after) : WAdm_weights_loop iter out = ok after := by
  rw [loop_normalize,Aeneas.Std.loop.eq_def]
  have h : sourceStep (iter,out) = ok (cont (next,mid)) := step
  rw [h]
  exact (loop_normalize next mid).symm.trans tail

theorem loop_list (xs : List K) (property : xs.length ≤ Usize.max) (out : alloc.vec.Vec U8)
    (bound : out.val.length + 16 * xs.length ≤ Usize.max) :
    ∃ after, WAdm_weights_loop ⟨xs,property⟩ out = ok after ∧
      after.val = out.val ++ xs.flatMap CheckpointP6EncodeK.bytes := by
  induction xs generalizing out with
  | nil =>
    refine ⟨out,?_,by simp⟩
    unfold WAdm_weights_loop
    rw [Aeneas.Std.loop.eq_def]
    rfl
  | cons x xs ih =>
    have first : out.val.length + 16 ≤ Usize.max := by
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at bound
      omega
    obtain ⟨mid,call,midval⟩ := put_k out x first
    have restProperty : xs.length ≤ Usize.max := by simp only [List.length_cons] at property; omega
    have restBound : mid.val.length + 16 * xs.length ≤ Usize.max := by
      rw [midval,List.length_append,k_length]
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at bound
      omega
    obtain ⟨after,tail,afterval⟩ := ih restProperty mid restBound
    have step : WAdm_weights_loop.body ⟨x::xs,property⟩ out =
        ok (cont ((⟨xs,restProperty⟩ : alloc.vec.into_iter.IntoIter K),mid)) := by
      change (do let v ← WAdm_putK out x; ok (cont ((⟨xs,restProperty⟩ : alloc.vec.into_iter.IntoIter K),v))) = _
      rw [call]
      rfl
    refine ⟨after,?_,?_⟩
    · exact loop_step _ _ _ _ _ step tail
    · rw [afterval,midval,List.flatMap_cons,List.append_assoc]

theorem weights (xs : alloc.vec.Vec K) (out : alloc.vec.Vec U8)
    (bound : out.val.length + 16 * xs.val.length ≤ Usize.max) :
    ∃ after, WAdm_weights out xs = ok after ∧
      after.val = out.val ++ xs.val.flatMap CheckpointP6EncodeK.bytes := by
  rcases xs with ⟨xs,property⟩
  simpa only [WAdm_weights,alloc.vec.IntoIteratorVec.into_iter,bind_tc_ok] using
    loop_list xs property out bound

#print axioms loop_normalize
#print axioms loop_step
#print axioms loop_list
#print axioms weights
end AspisR1.WAdm_WeightsHelpers
end
