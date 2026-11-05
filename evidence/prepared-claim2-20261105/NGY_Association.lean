import NGY_Loop
import NGY_SourceStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGY_Association
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort
open AspisR1CurrentPreparedClaim

/-- One SAME-carrier read/child/log/control transition, with the child and
poststate derived, never a whole native output-equality assumption. -/
theorem step {H : Type} (inst : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array Concrete.E 29#usize)
 (point lane : Usize) (iter iter' : ClaimScalar.Range)
 (domain : NGU_LPq_PointConstruct.ReadDomain sem y1 g point)
 (before : Native) (hl : lane.val<29)
 (bounded : NGU_LPm_PublicFold.Bounded before lane.val)
 (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some lane,iter')) :
 ∃ value scalar after,
  canonE value ∧ canonQ scalar ∧
  ClaimScalar.read NGU_LPm_PointLoop.ops sem y1 point lane=ok (qPort scalar) ∧
  Array.index_usize g lane=ok (ePort value) ∧
  FIo_Native.fast_pairing.EbyKDot.push before value scalar=ok (.Ok (),after) ∧
  NGU_LPm_PublicFold.Bounded after (lane.val+1) ∧
  NGY_Oracle.reference lane.val before after value scalar (.Ok ())=
   (.advance (lane.val+1),after,[⟨value,scalar,before,after,.Ok ()⟩]) ∧
  verifier.prepared_claim_dot_loop.body NGU_LPm_PointLoop.ops inst y1 g iter sem point (statePort before)=
   ok (NGY_SourceStep.outcome iter' sem point (statePort after) (.Ok ())) := by
 obtain ⟨v,q,after,cv,cq,read,weight,push,bnext,log⟩ :=
  NGY_Loop.installed_step sem y1 g point lane domain before hl bounded
 have count : before.count.val<29 := by rw [bounded.1]; exact hl
 have child := NGU_LPm_PointLoop.model_push before after v q cv cq count push
 exact ⟨v,q,after,cv,cq,read,weight,push,bnext,log,
  NGY_SourceStep.source NGU_LPm_PointLoop.ops inst sem y1 g iter iter' point lane
   (statePort before) (statePort after) (ePort v) (qPort q) (.Ok ()) next read weight child⟩

#print axioms step
end AspisR1.NGY_Association
end
