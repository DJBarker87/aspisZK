import NNG_InstallBase
import NNG_EmittedContext
import NJM_InvocationRoots
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

/-- The CLOSED134 root is instantiated on the SAME original parser bytes and
transcript. Its retained native Cut is P6 tool transport; no child Result or
successful endpoint is assumed. Full ordered digest logs stay in the run. -/
theorem source {H : Type} (native : NJM_RoundsCut.Observations)
 (cut : NJM_RoundsCut.Cut native) (token frame : Nat)
 (d : aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (t : r1_wire.SemanticTranscript H) :
 match parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
 | .ok (.Ok pre) =>
   ∃ running,
    outer (inner lowerReply toT13)
     (rounds d (fromT12 (AspisR1PublicPreparation.PrefixAdapter.fromOld pre)) t)=
    (NJM_RoundsInduction.chain native token frame (NNG_Install.digest d)
     (AspisR1PublicPreparation.PrefixAdapter.fromOld pre) NJG_RoundsCode.sites
      (running,Array.repeat 10#usize AspisR1PublicPreparation.aspis_core.field.QM31.ZERO,toT10 t)).2 ∧
    AspisR1PublicPreparation.PreparedHashCode.run
     (AspisR1PublicPreparation.S1SemanticCode.rounds NJM_RoundJoin.R (NNG_Install.digest d)
      (AspisR1PublicPreparation.PrefixAdapter.fromOld pre) (toT10 t))=
    NJM_RoundsInduction.chain native token frame (NNG_Install.digest d)
     (AspisR1PublicPreparation.PrefixAdapter.fromOld pre) NJG_RoundsCode.sites
      (running,Array.repeat 10#usize AspisR1PublicPreparation.aspis_core.field.QM31.ZERO,toT10 t)
 | _ => True := by
 have closed := NJM_InvocationRoots.rounds native cut token frame (NNG_Install.digest d) bytes (toT10 t)
 split
 · rename_i pre parsed
   rw [parsed] at closed
   obtain ⟨running,runEq⟩ := closed.1
   refine ⟨running,?_,runEq⟩
   rw [same,fromT12_inverse]
   exact congrArg Prod.snd runEq
 · trivial
 · trivial
 · trivial
#print axioms source
end AspisR1.NNG_InstallRounds
