import NGY_Result
import NGY_Association
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGY_Complete
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort
open AspisR1CurrentPreparedClaim

/-- Complete per-step hand-transcribed reference-to-cohort association. The
local ReadDomain and Bounded invariant derive every child domain and state;
there is no final native output or arbitrary-success premise. -/
theorem step {H : Type} (inst : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array Concrete.E 29#usize)
 (point lane : Usize) (iter iter' : ClaimScalar.Range)
 (domain : NGU_LPq_PointConstruct.ReadDomain sem y1 g point)
 (before : Native) (hl : lane.val<29)
 (bounded : NGU_LPm_PublicFold.Bounded before lane.val)
 (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some lane,iter')) :
 ∃ value scalar after,
  canonE value ∧ canonQ scalar ∧ before.count.val<29 ∧
  ClaimScalar.read NGU_LPm_PointLoop.ops sem y1 point lane=ok (qPort scalar) ∧
  Array.index_usize g lane=ok (ePort value) ∧
  FIo_Native.fast_pairing.EbyKDot.push before value scalar=ok (.Ok (),after) ∧
  NGU_LPm_PublicFold.Bounded after (lane.val+1) ∧
  NGY_Result.reference lane.val before after value scalar (.Ok ())=
   (core.result.Result.Ok (), NGY_Oracle.Control.advance (lane.val+1),
    after,[NGY_Oracle.Entry.mk value scalar before after (.Ok ())]) ∧
  verifier.prepared_claim_dot_loop.body NGU_LPm_PointLoop.ops inst y1 g iter sem point (statePort before)=
   ok (NGY_SourceStep.outcome iter' sem point (statePort after) (.Ok ())) := by
 obtain ⟨v,q,after,cv,cq,read,weight,push,bnext,log,body⟩ :=
  NGY_Association.step inst sem y1 g point lane iter iter' domain before hl bounded next
 have count : before.count.val<29 := by rw [bounded.1]; exact hl
 exact ⟨v,q,after,cv,cq,count,read,weight,push,bnext,NGY_Result.success _ _ _ _ _,body⟩

#print axioms step
end AspisR1.NGY_Complete
end
