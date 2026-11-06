import NLP_C04Effects
set_option autoImplicit false
noncomputable section
namespace NLP_C04Reply
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Lift only the adopted observation, preserving panic/divergence explicitly. -/
def lift : Result Unit → R Unit
 | .ok u => .ok (.Ok u)
 | .fail error => .fail error
 | .div => .div
theorem relation (out : NLL.Reply) :
 NLB_ErrorTransport.ReplyRel (NHT_ResultPort.action (ok out))
  (lift (NKV_ParentSource.observe (ok out))) := by
 cases out with
 | Ok u => exact .same _
 | Err error => exact .rejected (NHT_ResultPort.error error)
/-- At the SAME returning native C04 cut, exact Result relation and the
adopted ordered digest history come from the same complete child packet. -/
theorem at_actual (H : Bytes → State) (wr rr : NP6_StdModel.Reservation) (finish : Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (root0Input : NLP_InputDomain.Root0 ck proof)
 (pr : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (reply : R Unit)
 (entered : Event.merkle pr p folded reply∈(run wr rr (NLP_NativeMerkle.action H) finish d pub proof ck hash none).events) :
 ∀ (history : NLL.History) (out : NLL.Reply),
 NLL_BatchSource.Invocation H pr p folded 1#usize history out →
 let observed:=NLL_ObservedCalls.calls H pr (NLP_RootCodec.parsed pr (Port3_BatchStage.root1 p))
  p.queries 1#usize (NLL_Parent.sites (NLL_BatchSource.roots p folded))
  NKV_ParentSource.zeroI NKV_ParentSource.zeroV
 observed.1=history ∧ NLB_ErrorTransport.ReplyRel reply (lift observed.2) := by
 intro history out native
 obtain ⟨replyLaw,_,observed⟩:=NLP_C04Effects.returning H wr rr finish d pub proof ck hash
  len root0Input pr p folded reply entered history out native
 dsimp only
 rw [observed,replyLaw]
 exact ⟨rfl,relation out⟩
set_option pp.proofs false
#print lift
#print relation
#print at_actual
#print axioms relation
#print axioms at_actual
end NLP_C04Reply
