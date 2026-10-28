import NDH_TranscriptReference.Funs
import AspisR1PublicPreparation.Funs
import NDH_ResultLaws
set_option autoImplicit false
namespace NDH_TranscriptBridge
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

def port {H : Type} (D : aspis_core.Digest32 H) : NDH_TranscriptReference.NDH_DigestRef H :=
  ⟨D.coremarkerCopyInst,D.digest⟩

theorem new_reference {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (semantic : Array U8 32#usize) (variant : transport.Variant) :
    (do let tag ← transport.Variant.tag variant
        let (state,hash1) ← NDH_TranscriptReference.new_ref (port D) hash semantic tag
        ok (transcript.Transcript.mk state hash1)) =
      transcript.Transcript.new D hash semantic variant := by
  cases variant <;>
    simp only [NDH_TranscriptReference.new_ref, port, transcript.Transcript.new,
      transport.Variant.tag, lift, bind_tc_ok, NDH_ResultLaws.assoc]

theorem absorb_reference {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    (do let state ← NDH_TranscriptReference.absorb_ref (port D) self.hash self.state row payload
        ok {self with state := state}) =
      transcript.Transcript.absorb D self row payload := by
  simp only [NDH_TranscriptReference.absorb_ref, port, transcript.Transcript.absorb,
    lift, bind_tc_ok, NDH_ResultLaws.assoc]

#print axioms new_reference
#print axioms absorb_reference
end NDH_TranscriptBridge
