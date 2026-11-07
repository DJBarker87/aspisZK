import NNC_WeakSpec
import TAS_Interfaces
set_option autoImplicit false
noncomputable section
namespace NNC_WriteFree
open Aeneas Aeneas.Std AspisR1 VTop_Stages NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Observable verifier events. Account writes cannot be constructed in this
carrier. The concrete interpreter must still transport every actual effect,
including stopped-child prefixes; choosing an empty renderer is not that proof. -/
abbrev ReadEvent := {e : RSL.Event // ∀ c b, e ≠ RSL.Event.write c b}
abbrev Renderer (Ambient X : Type) (H : Bytes → State) :=
 ∀ s : Frame Ambient X, End H s.args → List (Event Ambient X) → RSL.Env → List ReadEvent

def render {Ambient X : Type} {H : Bytes → State} (r : Renderer Ambient X H) :
 NNC_WeakSpec.Render Ambient X H := fun s o es env => (r s o es env).map Subtype.val

def law {Ambient X : Type} (H : Bytes → State) (d : aspis_core.digest.Digest32 X)
 (hash : X) (world : NLM_PacketTypes.World Ambient) (r : Renderer Ambient X H)
 (pub proof ck : RSL.Bytes) : RSL.Spec (Except verifier.Error Unit) :=
 NNC_WeakSpec.w H d hash world (render r) pub proof ck

theorem render_no_write {Ambient X : Type} {H : Bytes → State}
 (r : Renderer Ambient X H) (s : Frame Ambient X) (o : End H s.args)
 (es : List (Event Ambient X)) (env : RSL.Env) (c : Nat) (b : RSL.Bytes) :
 RSL.Event.write c b ∉ render r s o es env := by
 intro member
 obtain ⟨e,_,equal⟩ := List.mem_map.mp member
 exact e.property c b equal

/-- The amended weak law is write-free on ALL inputs and ALL exits,
including rejected, aborted, diverging and independently stopped outcomes. -/
theorem writeFree {Ambient X : Type} (H : Bytes → State)
 (d : aspis_core.digest.Digest32 X) (hash : X)
 (world : NLM_PacketTypes.World Ambient) (r : Renderer Ambient X H)
 (pub proof ck : RSL.Bytes) : RSL.TAS.WriteFree (law H d hash world r pub proof ck) := by
 intro env observed admitted c b
 obtain ⟨pu,pr,cp,_,_,_,outcome,es,_,output⟩ := admitted
 subst observed
 exact render_no_write r _ outcome es env c b

theorem contains_native {Ambient X : Type} (H : Bytes → State)
 (s : Frame Ambient X) (r : Renderer Ambient X H)
 (outcome : End H s.args) (events : List (Event Ambient X))
 (native : NMN_064.Native H s outcome events) (env : RSL.Env) :
 law H s.args.digest s.args.hash s.world r
  (NNC_ByteCarriers.host s.args.publicBytes.val) (NNC_ByteCarriers.host s.args.proof.val)
  (NNC_ByteCarriers.host s.args.checkpoint.val) env
  ⟨NNC_WeakSpec.exit H s.args outcome,render r s outcome events env⟩ :=
 NNC_WeakSpec.contains_native H s (render r) outcome events native env

#print axioms render_no_write
#print axioms writeFree
#print axioms contains_native
end NNC_WriteFree
