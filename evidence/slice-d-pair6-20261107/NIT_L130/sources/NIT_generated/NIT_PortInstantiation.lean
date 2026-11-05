import NIT_ResultCanonical
import NIT_FinishComposition
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_PortInstantiation
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2

/-- The model-chain canonical invariant discharges the native PairPort reply
pre-state on every returning error/success, not merely on successful pair. -/
theorem canonical_reply (reply : NIT_ErrorTransport.NativeReply E)
 (canonical : NIT_ResultCanonical.Canonical (ok reply)) :
 replyCanonical (NIT_ErrorTransport.reply reply) := by
 cases reply with
 | Err e=>trivial
 | Ok value=>exact canonical

/-- Local record witness at the actual PairPort call. This supplies no native
whole-pair certificate and does not identify arbitrary owner payloads. -/
theorem pair_port (owner alpha message : Nat) (p : verifier.Prepared)
 (s2 : p.variant=transport.Variant.S2) (ca : alphaCanonical p) (ck : feCanonical p.kappa)
 (reply : NIT_ErrorTransport.NativeReply E)
 (canonical : NIT_ResultCanonical.Canonical (ok reply)) :
 ∃ l : PairPort,l.reply=NIT_ErrorTransport.reply reply ∧
 cutPairPort owner alpha message p l (NIT_ErrorTransport.reply reply) owner := by
 let l : PairPort:=⟨owner,alpha,2,message,2048,p.kappa,NIT_ErrorTransport.reply reply,1⟩
 exact ⟨l,rfl,⟨s2,ca,ck,canonical_reply reply canonical,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩

#print axioms canonical_reply
#print axioms pair_port
end AspisR1.NIT_PortInstantiation
