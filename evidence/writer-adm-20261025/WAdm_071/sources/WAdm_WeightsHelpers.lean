import WAdm_ArrayHelpers
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1.WAdm_WeightsHelpers
open WAdm_Fissioned WAdm_model WAdm_EmittedScalars

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
    refine ⟨after,?_,?_⟩
    · unfold WAdm_weights_loop
      rw [Aeneas.Std.loop.eq_def]
      simp only [WAdm_weights_loop.body,alloc.vec.into_iter.IteratorIntoIter.next,call,bind_tc_ok]
      exact tail
    · rw [afterval,midval,List.flatMap_cons,List.append_assoc]

theorem weights (xs : alloc.vec.Vec K) (out : alloc.vec.Vec U8)
    (bound : out.val.length + 16 * xs.val.length ≤ Usize.max) :
    ∃ after, WAdm_weights out xs = ok after ∧
      after.val = out.val ++ xs.val.flatMap CheckpointP6EncodeK.bytes := by
  simpa only [WAdm_weights,alloc.vec.IntoIteratorVec.into_iter,bind_tc_ok] using
    loop_list xs.val xs.property out bound

#print axioms loop_list
#print axioms weights
end AspisR1.WAdm_WeightsHelpers
end
