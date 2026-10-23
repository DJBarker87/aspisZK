import S2H_ReferencePorts
import S2G_Children
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2H
open S2E S2E_Reference.S2E_Reference

/-- Value facts attached to cuts DERIVED from a single extracted execution.
This does not supply G's still-missing native Box/Vec/effect interpretations. -/
structure InstalledAt {C S : Type} (eops : S2E_Reference.Ops)
    (remaining : Children C S) (ops : SdkReference.Ops) (vops : AspisR1CurrentCaller.Ops)
    (o : Original S) (state : S) (sdk : SDK)
    (c : ReferenceCertificate eops (S2G.Children.installValues remaining ops vops) o state sdk) : Prop where
  publicLength : c.publicBytes.val.length = 1880
  validator : SourceInstallation.actualValidator c.statement = ok (.Ok ())
  encoder : AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
    (CurrentCarrier.toDecoderAfterstate (commonOf c.statement).lane_transition.candidate_afterstate) =
      ok (.Ok c.candidate)
  first : AspisR1CurrentCaller.verifier.candidate.tx1 vops
    (SourceInstallation.currentDigest
      (SdkReference.SolanaDigest.Insts.Aspis_coreDigestDigest32 (SdkReference.Installation.install ops vops)))
    (CurrentCarrier.toCurrentPublic (SdkReference.ReadyStatement.publicOf c.statement))
    c.publicBytes.deref c.selected c.split () none = ok (.Ok c.checkpoint)

/-- Uses G's proved contracts only in their stated PURE value scope. The seven
unfilled callbacks remain literally `remaining`; success of each is obtained
from this one reference run, never independent accepted-child hypotheses.
The full child implementations/effect ports are not inferred from this result. -/
theorem installed_reference_certificate {C S : Type} (eops : S2E_Reference.Ops)
    (remaining : Children C S) (ops : SdkReference.Ops) (vops : AspisR1CurrentCaller.Ops)
    (o : Original S) (state : S) (sdk : SDK)
    (accepted : evalStage1 eops (S2G.Children.installValues remaining ops vops) o =
      ok (.Ok (),state,sdk)) :
    ∃ c : ReferenceCertificate eops (S2G.Children.installValues remaining ops vops) o state sdk,
      InstalledAt eops remaining ops vops o state sdk c := by
  obtain ⟨c⟩ := evalStage1_certificate eops (S2G.Children.installValues remaining ops vops) o state sdk accepted
  have decode := S2G.Children.liftValue_success o.state c.afterDecode
    (S2G.decode ops vops c.publicBytes.deref) (.Ok c.statement) c.decoded
  have facts := S2G.decode_contract ops vops c.publicBytes.deref c.statement decode.1
  have candidate := S2G.Children.liftValue_success c.afterValidate c.afterEncode
    (S2G.candidate (commonOf c.statement).lane_transition.candidate_afterstate) (.Ok c.candidate) c.encoded
  have first := S2G.Children.liftValue_success c.afterEncode c.afterFirst
    (S2G.first ops vops c.statement c.publicBytes.deref c.selected c.split)
    (.Ok c.checkpoint) c.firstReturned
  exact ⟨c,{
    publicLength:=facts.1,
    validator:=S2G.validate_contract c.statement facts.2.1,
    encoder:=S2G.candidate_contract _ c.candidate candidate.1,
    first:=S2G.first_contract ops vops c.statement c.publicBytes.deref c.selected c.split c.checkpoint first.1 }⟩

#print axioms installed_reference_certificate
end AspisR1.S2H
