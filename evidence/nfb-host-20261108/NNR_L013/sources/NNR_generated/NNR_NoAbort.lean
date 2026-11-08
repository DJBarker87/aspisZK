import NNR_CommonReturned
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_NoAbort
open Aeneas Aeneas.Std Result VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NLT_NativeInvocation

theorem child (H : Bytes → State) (pr : Slice U8) (p : verifier.Prepared)
 (folded : Array U8 32#usize) (reply : R Unit)
 (detail : NLT_Subcuts.Detail H (.merkle pr p folded reply))
 (returned : ∃ u, reply = .ok u) :
 ∃ inside out, NLL_BatchSource.Invocation H pr p folded 1#usize inside out := by
 cases detail with
 | ordinary e notMerkle => exact False.elim (notMerkle pr p folded reply rfl)
 | returning pr p folded reply inside out native => exact ⟨inside,out,native⟩
 | aborting pr p folded error inside pending native =>
  obtain ⟨u,h⟩ := returned
  cases h

theorem returned (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length = 57607)
 (value : core.result.Result Unit verifier.Error) (records : List (Occurrence H d hash))
 (native : Invocation H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) (.ok value) records)
 (record : Occurrence H d hash) (member : record ∈ records) :
 NNR_ReturnedLog.Returned (actual record) := by
 let f := NLT_FrameFromCuts.frame records
 have joined := NLT_NativeSource.source H d pub proof ck hash len (.ok value) records native
 have result : (run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none).result = .ok value := by
  rw [NJU_CommonObserved.source]
  exact joined.1.symm
 exact NNR_CommonReturned.safe f.resume f.pending (NLP_NativeMerkle.action H)
  (NLB_Parent.finish f.finish) d pub proof ck hash value result (actual record)
  (NLT_NativeFacts.member H d pub proof ck hash len (.ok value) records native record member)
#print axioms child
#print axioms returned
end AspisR1.NNR_NoAbort
end
