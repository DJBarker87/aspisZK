import XSc_PushFrame
import XRl_LoopInvariant
import XSc_RangeMeasure
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSc_PushLoopFrame
abbrev S := core.ops.range.Range Usize × verifier.BatchedWeights
/-- The emitted row loop preserves pending shape and terms on its own successful
execution. It does not assume canonical basis entries or successful pushes. -/
theorem source (v : alloc.vec.Vec aspis_core.field.QM31) (q : aspis_core.field.QM31)
 (i width : Usize) (basis : Array aspis_core.field.M31 256#usize)
 (iter : core.ops.range.Range Usize) (before after : verifier.BatchedWeights)
 (run : verifier.accumulate_batched_with_node_loop1 iter v q i before width basis=ok after) :
 after.raw.val.length=before.raw.val.length ∧ after.terms=before.terms := by
 unfold verifier.accumulate_batched_with_node_loop1 at run
 apply XRl_LoopInvariant.preserve _
  (fun s : S => s.2.raw.val.length=before.raw.val.length ∧ s.2.terms=before.terms)
  (fun out => out.raw.val.length=before.raw.val.length ∧ out.terms=before.terms)
  (fun s => XSc_RangeMeasure.remaining s.1) ?_ (iter,before) after ⟨rfl,rfl⟩ run
 intro s r inv hr
 rcases s with ⟨iter,weights⟩
 unfold verifier.accumulate_batched_with_node_loop1.body at hr
 obtain ⟨o,next,hn,hr⟩ := pair_bind_success _ _ _ hr
 cases o with
 | none =>
  cases Result.ok.inj hr
  exact inv
 | some j =>
  obtain ⟨m,_,hr⟩ := bind_success _ _ _ hr
  obtain ⟨weights1,hpush,hr⟩ := bind_success _ _ _ hr
  obtain ⟨_,_,hr⟩ := bind_success _ _ _ hr
  obtain ⟨_,_,hr⟩ := bind_success _ _ _ hr
  obtain ⟨_,_,hr⟩ := bind_success _ _ _ hr
  obtain ⟨_,_,hr⟩ := bind_success _ _ _ hr
  obtain ⟨_,_,hr⟩ := bind_success _ _ _ hr
  obtain ⟨_,_,hr⟩ := bind_success _ _ _ hr
  obtain ⟨_,_,hr⟩ := bind_success _ _ _ hr
  obtain ⟨_,_,hr⟩ := bind_success _ _ _ hr
  cases Result.ok.inj hr
  have frame := XSc_PushFrame.source weights weights1 j q m hpush
  have decrease := XSc_RangeMeasure.advance iter next j hn
  exact ⟨⟨frame.1.trans inv.1,frame.2.trans inv.2⟩,by dsimp only; omega⟩
#print axioms source
end XSc_PushLoopFrame
