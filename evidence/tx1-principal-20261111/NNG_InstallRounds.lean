import NNG_InstallBase
import NNG_EmittedContext
import NJM_InvocationRoots
import NLU_InputDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_InstallRounds
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer inner outer_inverse inner_inverse)
open AspisR1.NMT_Transport (arr arr_inverse)
abbrev OldQ := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev OldT (H : Type) := AspisR1PublicPreparation.r1_wire.SemanticTranscript H
abbrev OldReply (H : Type) := OldQ × Array OldQ 10#usize × OldT H
abbrev Reply (H : Type) := Q × Alpha × r1_wire.SemanticTranscript H

def raiseReply {H : Type} (r : OldReply H) : Reply H :=
 ⟨fromT1 r.1,arr fromT1 r.2.1,fromT10 r.2.2⟩
def lowerReply {H : Type} (r : Reply H) : OldReply H :=
 ⟨toT1 r.1,arr toT1 r.2.1,toT10 r.2.2⟩
theorem roundtrip {H : Type} (r : OldReply H) : lowerReply (raiseReply r)=r := by
 rcases r with ⟨q,a,t⟩
 simp only [lowerReply,raiseReply,fromT1_inverse,fromT10_inverse]
 rw [arr_inverse fromT1 toT1 fromT1_inverse]
#print axioms roundtrip

def rounds {H : Type} (d : aspis_core.digest.Digest32 H)
 (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) :
 Result (core.result.Result (Reply H) r1_wire.Error) :=
 outer (inner raiseReply fromT13)
  (AspisR1PublicPreparation.PreparedHashCode.run
   (AspisR1PublicPreparation.S1SemanticCode.rounds NJM_RoundJoin.R
    (NNG_Install.digest d) (toT12 p) (toT10 t))).2

theorem same {H : Type} (d : aspis_core.digest.Digest32 H)
 (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) :
 outer (inner lowerReply toT13) (rounds d p t)=
 (AspisR1PublicPreparation.PreparedHashCode.run
   (AspisR1PublicPreparation.S1SemanticCode.rounds NJM_RoundJoin.R
    (NNG_Install.digest d) (toT12 p) (toT10 t))).2 := by
 apply outer_inverse
 intro r
 exact inner_inverse raiseReply lowerReply fromT13 toT13 roundtrip fromT13_inverse r
#print axioms same

/-- CLOSED134's source companion (the complete source theorem used by
NJM_InvocationRoots.rounds), instantiated from the row's own Prefix provenance.
No child Result, endpoint or operation dictionary is a hypothesis. The reviewed
native Cut remains exactly the inherited P6 transport boundary. -/
theorem source {H : Type} (native : NJM_RoundsCut.Observations)
 (cut : NJM_RoundsCut.Cut native) (token frame : Nat)
 (d : aspis_core.digest.Digest32 H) (p : r1_wire.Prefix)
 (t : r1_wire.SemanticTranscript H) (hd : NLU.ParsedPrefix (toT12 p)) :
 ∃ running,
  outer (inner lowerReply toT13) (rounds d p t)=
  (NJM_RoundsInduction.chain native token frame (NNG_Install.digest d)
   (toT12 p) NJG_RoundsCode.sites
   (running,Array.repeat 10#usize AspisR1PublicPreparation.aspis_core.field.QM31.ZERO,toT10 t)).2 ∧
  AspisR1PublicPreparation.PreparedHashCode.run
   (AspisR1PublicPreparation.S1SemanticCode.rounds NJM_RoundJoin.R (NNG_Install.digest d)
    (toT12 p) (toT10 t))=
  NJM_RoundsInduction.chain native token frame (NNG_Install.digest d)
   (toT12 p) NJG_RoundsCode.sites
   (running,Array.repeat 10#usize AspisR1PublicPreparation.aspis_core.field.QM31.ZERO,toT10 t) := by
 obtain ⟨bytes,pre,parsed,prefixEq⟩ := hd
 obtain ⟨running,runEq,children⟩ := NJM_RoundsClosed.source native cut token frame
  (NNG_Install.digest d) bytes pre parsed (toT10 t)
 refine ⟨running,?_,?_⟩
 · rw [same,prefixEq]
   exact congrArg Prod.snd runEq
 · rw [prefixEq]
   exact runEq
#print axioms source
end AspisR1.NNG_InstallRounds
