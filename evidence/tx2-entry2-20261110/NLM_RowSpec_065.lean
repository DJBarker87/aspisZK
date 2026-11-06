import NJU_CommonObserved
import NLM_PacketTypes
set_option autoImplicit false
noncomputable section
namespace NLM_RowSpec_065
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLM_PacketTypes
structure Frame (H : Type) where
 digest : aspis_core.digest.Digest32 H
 publicBytes : Slice U8
 proof : Slice U8
 checkpoint : Slice U8
 hash : H
abbrev Reply := core.result.Result Unit verifier.Error
abbrev Native (Ambient : Type) := ∀ {H : Type}, Frame H → World Ambient →
 Observation Ambient NJU_CommonObserved.Event Reply
/-- The inherited native resume scope; callers must derive it from their
SAME parse and encoder calls. No new domain is imposed on checkpoint. -/
def Domain {H : Type} (f : Frame H) : Prop :=
 f.proof.val.length=57607 ∧ f.publicBytes.val.length≤1880
/-- Draft OPEN-065 invocation interface: complete source chronological
Run, every Result arm and external post-frame, at original decoded arguments.
The source's nested child-law/internal-effect installation remains with 065's
owner; this definition is an intermediate review input, never a row root. -/
def RowSpec_065 {Ambient : Type} (native : Native Ambient)
 (wr rr : NP6_StdModel.Reservation) (merkle : NJJ_Common.Merkle) (finish : NJJ_Common.Finish) : Prop :=
 ∀ {H : Type} (f : Frame H) (world : World Ambient), Domain f →
 native f world=⟨world,NJU_CommonObserved.run wr rr merkle finish f.digest
   f.publicBytes f.proof f.checkpoint f.hash none⟩ ∧
 (native f world).run.result=NJJ_Common.run wr rr merkle finish f.digest
   f.publicBytes f.proof f.checkpoint f.hash none
#print RowSpec_065
end NLM_RowSpec_065
