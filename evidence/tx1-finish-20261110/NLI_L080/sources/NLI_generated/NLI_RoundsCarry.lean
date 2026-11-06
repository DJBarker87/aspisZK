import NLI_RoundsHash
import NJM_InvocationRoots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_RoundsCarry
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NJG_RoundsCode
open NIX_CertificateFrames NJG_NativeCuts
open PreparedHashCode (run Log)
abbrev Native := RoundOutput → RoundOutput
/-- Return ABI portion of the reviewed NLI rounds windows. The input-view
and physical frame portions are separate and must also be installed. This is
NOT a complete136 cut or a row root. -/
def Cut (native : Native) : Prop := ∀ reply,native reply=reply
/-- The child is instantiated first; fail/div stop at its entered prefix and
never fabricate a Rust return. Only a returning child enters native carry G. -/
def afterChild {H : Type} (native : Native) (hash : H)
 (child : Log × Result (Output H)) : Log × Result (Output H) :=
 match child.2 with
 | .fail e => (child.1,.fail e)
 | .div => (child.1,.div)
 | .ok reply => (child.1,ok (NJM_RoundsTransport.raise hash (native (NJM_RoundsTransport.lower reply))))
/-- Full Result/log transport at the SAME parsed prefix and transcript.
The immutable hash law is derived from the original ten-round source. -/
theorem source {H : Type} (native : Native) (cut : Cut native)
 (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (before : r1_wire.SemanticTranscript H) :
 afterChild native before.hash (run (S1SemanticCode.rounds NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) before))=
 run (S1SemanticCode.rounds NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) before) := by
 have framed:=NLI_RoundsHash.source D bytes pre parsed before
 generalize call : run (S1SemanticCode.rounds NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) before)=child at framed ⊢
 rcases child with ⟨log,reply⟩
 cases reply with
 | fail e => rfl
 | div => rfl
 | ok reply =>
  change NJM_RoundsTransport.Frame before.hash reply at framed
  change (log,ok (NJM_RoundsTransport.raise before.hash (native (NJM_RoundsTransport.lower reply))))=(log,ok reply)
  rw [cut, NJM_RoundsTransport.roundtrip before.hash reply framed]
/-- The CLOSED134 native chain is consumed at the ORIGINAL child arguments.
Its initialization witness is produced internally, never supplied by a caller.
This transports its full returned carrier, not the missing136 parent heap. -/
theorem from_child {H : Type} (native : Native) (cut : Cut native)
 (childNative : NJM_RoundsCut.Observations) (childCut : NJM_RoundsCut.Cut childNative)
 (token frame : Nat) (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (before : r1_wire.SemanticTranscript H) :
 ∃ running,
 afterChild native before.hash (NJM_RoundsInduction.chain childNative token frame D (PrefixAdapter.fromOld pre) sites
  (running,Array.repeat 10#usize aspis_core.field.QM31.ZERO,before))=
 run (S1SemanticCode.rounds NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) before) := by
 obtain ⟨running,whole⟩:=NJM_RoundsInduction.rounds childNative childCut token frame D bytes pre parsed before
 refine ⟨running,?_⟩
 rw [←whole]
 exact source native cut D bytes pre parsed before
#print axioms source
#print axioms from_child
#print from_child
end AspisR1.NLI_RoundsCarry
end
