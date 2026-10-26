import RawK_InitHead
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_InitCall
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem reached {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (pub : Slice U8) (root : Array U8 32#usize) (out : r1_wire.SemanticTranscript H)
    (success : erase (S1SemanticCode.newTranscript D hash pub root) = ok (.Ok out)) :
    ∃ (len : U32) (state : State),
      core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len pub)=ok (.Ok len) ∧
      RawK_Head.head (S1SemanticCode.newTranscript D hash pub root)=
        some (flatten (RawJ_DigestRead.initParts pub len root),state) := by
  let log := RawK_Head.head (S1SemanticCode.newTranscript D hash pub root)
  have inc : ∀ entry, RawK_Head.head (S1SemanticCode.newTranscript D hash pub root)=some entry →
      log=some entry := fun _ h=>h
  change ∃ len state, _ ∧ log=_
  unfold S1SemanticCode.newTranscript at success inc
  obtain ⟨r,hr,s1,sub1⟩ := RawK_Head.right _ _ _ success
  obtain ⟨r1,hr1,s2,sub2⟩ := RawK_Head.right _ _ _ s1
  obtain ⟨cf,hcf,s3,sub3⟩ := RawK_Head.right _ _ _ s2
  cases cf with
  | Break residual =>
    rw [erase_lift] at s3
    repeat' first | (solve | cases s3) | uncase_result | head_reduce s3 | split at s3
  | Continue len =>
    have converted : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len pub)=ok (.Ok len) := by
      rw [erase_lift] at hr hr1 hcf
      cases r1 with
      | Err e => cases hcf
      | Ok n =>
        have same : n=len := core.ops.control_flow.ControlFlow.Continue.inj (Result.ok.inj hcf)
        subst n
        cases r with
        | Err e =>
          cases he : r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once D () e <;>
            simp [core.result.Result.map_err,he] at hr1
        | Ok n =>
          simp only [core.result.Result.map_err] at hr1
          have same : n=len := core.result.Result.Ok.inj (Result.ok.inj hr1)
          rw [same] at hr
          exact hr
    let parts := RawJ_DigestRead.initParts pub len root
    change erase (effects.digest D hash parts >>= fun state =>
      pure (core.result.Result.Ok ({state,hash,next_row:=0#u8} : r1_wire.SemanticTranscript H)))=
      ok (.Ok out) at s3
    obtain ⟨state,digest,tail,logs⟩ := AuS1_Trace.success_bind _ _ _ s3
    exact ⟨len,decodeState state,converted,inc _ (sub1 _ (sub2 _ (sub3 _
      (RawK_Head.left _ _ _ s3 _ (RawK_Head.digest_head D hash parts state digest)))))⟩

#print axioms reached
end AspisR1.F3U_InitCall
end
