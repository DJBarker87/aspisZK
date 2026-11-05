import NGY_FieldSpec
import NGY_Decoder
import NGY_Result
import NGY_SourceStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGY_FieldOracle
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort
open AspisR1CurrentPreparedClaim

inductive Event where
 | field (input : Slice U8) (lane : Usize) (reply : NE)
 | dot (entry : NGY_Oracle.Entry)

def reference (y1 : Slice U8) (lane : Usize) (before after : Native)
 (coefficient fieldReply : NE) (pushReply : core.result.Result Unit Unit) :=
 (NGY_Result.reference lane.val before after coefficient fieldReply.c0 pushReply,
  [Event.field y1 lane fieldReply,
   Event.dot ⟨coefficient,fieldReply.c0,before,after,pushReply⟩])

def G (y1 : Slice U8) (lane : Usize) (before after : Native)
 (coefficient fieldReply : NE) (pushReply : core.result.Result Unit Unit) :=
 (NGY_Result.G lane.val before after coefficient fieldReply.c0 pushReply,
  [Event.field y1 lane fieldReply,
   Event.dot ⟨coefficient,fieldReply.c0,before,after,pushReply⟩])

theorem association (y1 : Slice U8) (lane : Usize) (before after : Native)
 (coefficient fieldReply : NE) (pushReply : core.result.Result Unit Unit) :
 reference y1 lane before after coefficient fieldReply pushReply=
  G y1 lane before after coefficient fieldReply pushReply := by
 rw [reference,G,NGY_Result.association]

theorem error (y1 : Slice U8) (lane : Usize) (before after : Native)
 (coefficient fieldReply : NE) :
 (reference y1 lane before after coefficient fieldReply (.Err ())).1.1=
  core.result.Result.Err verifier.Error.Parse := rfl

/-- Substitute the CLOSED field child on the exact logged input, then the
CLOSED Dot child on its exact reply and SAME full prestate. Both poststate
and all child-domain facts are derived; no complete caller equality is input. -/
theorem source_step {H : Type} (inst : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (y1 : Slice U8)
 (domain : NGU_LPq_SelectedDomain.ByteDomain y1)
 (g : Array Concrete.E 29#usize) (weights : NGU_LPq_ReadPorts.WeightsCanonical g)
 (lane point : Usize) (hl : lane.val<29) (hp : point.val=5)
 (iter iter' : ClaimScalar.Range) (before : Native)
 (bounded : NGU_LPm_PublicFold.Bounded before lane.val)
 (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some lane,iter')) :
 ∃ b coefficient after,
  NGU_LPq_SelectedDomain.selected y1 lane=ok b ∧
  FIo_Native.weights.field y1 lane=ok (NGY_FieldSpec.value b) ∧
  canonE coefficient ∧ canonE (NGY_FieldSpec.value b) ∧
  Array.index_usize g lane=ok (ePort coefficient) ∧
  FIo_Native.fast_pairing.EbyKDot.push before coefficient (NGY_FieldSpec.value b).c0=
   ok (.Ok (),after) ∧
  NGU_LPm_PublicFold.Bounded after (lane.val+1) ∧
  reference y1 lane before after coefficient (NGY_FieldSpec.value b) (.Ok ())=
   G y1 lane before after coefficient (NGY_FieldSpec.value b) (.Ok ()) ∧
  verifier.prepared_claim_dot_loop.body NGU_LPm_PointLoop.ops inst y1 g iter sem point (statePort before)=
   ok (NGY_SourceStep.outcome iter' sem point (statePort after) (.Ok ())) := by
 obtain ⟨b,window,len,words⟩ := domain lane hl
 obtain ⟨field,cf⟩ := NGY_FieldSpec.source_local y1 lane b window len words
 obtain ⟨b2,window2,len2,cq,read⟩ := NGY_Decoder.selected sem y1 domain lane hl point hp
 have eq : b2=b := Result.ok.inj (window2.symm.trans window)
 subst b2
 have cq' : canonQ (NGY_FieldSpec.value b).c0 := cq
 have read' : ClaimScalar.read NGU_LPm_PointLoop.ops sem y1 point lane=
   ok (qPort (NGY_FieldSpec.value b).c0) := read
 obtain ⟨v,cv,weight⟩ := NGU_LPq_ReadPorts.weights g weights lane hl
 obtain ⟨after,push,bnext,rest⟩ := NGU_LPm_PublicFold.step before v (NGY_FieldSpec.value b).c0 lane.val hl bounded cv cq'
 have count : before.count.val<29 := by rw [bounded.1]; exact hl
 have model := NGU_LPm_PointLoop.model_push before after v (NGY_FieldSpec.value b).c0 cv cq' count push
 exact ⟨b,v,after,window,field,cv,cf,weight,push,bnext,association _ _ _ _ _ _ _,
  NGY_SourceStep.source NGU_LPm_PointLoop.ops inst sem y1 g iter iter' point lane
   (statePort before) (statePort after) (ePort v) (qPort (NGY_FieldSpec.value b).c0)
   (.Ok ()) next read' weight model⟩

#print axioms association
#print axioms error
#print axioms source_step
end AspisR1.NGY_FieldOracle
end
