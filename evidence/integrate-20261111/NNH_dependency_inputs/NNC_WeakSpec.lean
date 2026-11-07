import NNC_064Weak
import NNC_ByteCarriers
set_option autoImplicit false
noncomputable section
namespace NNC_WeakSpec
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Exact observable exit map, retaining Rust Err, fail, div and C04 stop. -/
def resultExit : NJU_CommonObserved.R Unit → RSL.Exit (Except verifier.Error Unit)
 | .ok (.Ok ())=>.ret (.ok ())
 | .ok (.Err e)=>.ret (.error e)
 | .fail _=>.abort
 | .div=>.diverge
def exit (H : Bytes → State) {X : Type} (a : Args X) : End H a → RSL.Exit (Except verifier.Error Unit)
 | .parseFail _=>.abort
 | .parseDiv=>.diverge
 | .parseReject e=>.ret (.error e)
 | .common (.resolved r _)=>resultExit r
 | .common (.c04Stopped _ _)=>.abort
/-- Representation of the ordered native trace is an adapter argument, not
an implementation or cryptographic assumption. A2 supplies its concrete
interpretation; this factory keeps the exact native trace as a witness. -/
abbrev Render (Ambient X : Type) (H : Bytes → State) :=
 ∀ s : Frame Ambient X,End H s.args → List (Event Ambient X) → RSL.Env → List RSL.Event
/-- The weak064 law in the exact V2Lib.tx2auth/ TCK.weaken shape. No Root0
predicate occurs. Trace rendering is explicit; this is not an A2 native
observation-transport theorem. All native outcomes, including stops, remain. -/
def w {Ambient X : Type} (H : Bytes → State) (d : aspis_core.digest.Digest32 X)
 (hash : X) (world : NLM_PacketTypes.World Ambient) (render : Render Ambient X H)
 (pub proof ck : RSL.Bytes) : RSL.Spec (Except verifier.Error Unit) :=
 fun env observed => ∃ (pu pr cp : Slice U8),
  NNC_ByteCarriers.host pu.val=pub ∧ NNC_ByteCarriers.host pr.val=proof ∧
  NNC_ByteCarriers.host cp.val=ck ∧
  ∃ outcome events,NMN_064.Native H ⟨⟨d,pu,pr,cp,hash⟩,world⟩ outcome events ∧
   observed=⟨exit H _ outcome,render ⟨⟨d,pu,pr,cp,hash⟩,world⟩ outcome events env⟩
/-- Every native outcome is admitted with exactly its projected Result and
ordered events. No successful-child or reference endpoint is assumed. -/
theorem contains_native {Ambient X : Type} (H : Bytes → State)
 (s : Frame Ambient X) (render : Render Ambient X H)
 (outcome : End H s.args) (events : List (Event Ambient X))
 (native : NMN_064.Native H s outcome events) (env : RSL.Env) :
 w H s.args.digest s.args.hash s.world render
  (NNC_ByteCarriers.host s.args.publicBytes.val) (NNC_ByteCarriers.host s.args.proof.val)
  (NNC_ByteCarriers.host s.args.checkpoint.val) env
  ⟨exit H s.args outcome,render s outcome events env⟩ :=
 ⟨s.args.publicBytes,s.args.proof,s.args.checkpoint,rfl,rfl,rfl,outcome,events,native,rfl⟩
theorem exit_ok (H : Bytes → State) {X : Type} (a : Args X) (outcome : End H a)
 (ok : exit H a outcome=.ret (.ok ())) :
 ∃ records,outcome=.common (.resolved (Aeneas.Std.Result.ok (.Ok ())) records) := by
 cases outcome with
 | parseFail e=>cases ok
 | parseDiv=>cases ok
 | parseReject e=>cases ok
 | common common=>
   cases common with
   | c04Stopped records cut=>cases ok
   | resolved r records=>
     cases r with
     | fail e=>cases ok
     | div=>cases ok
     | ok reply=>
       cases reply with
       | Err e=>cases ok
       | Ok unit=>cases unit;exact ⟨records,rfl⟩
/-- Weak-Spec accepted outputs imply matched digests, in native protocol byte
carriers. The caller supplies extents on its OWN byte inputs and the existing
runtime returning-value oracle interpretation. -/
theorem accepted_header {Ambient X : Type} (H : Bytes → State)
 (d : aspis_core.digest.Digest32 X) (hash : X) (world : NLM_PacketTypes.World Ambient)
 (render : Render Ambient X H) (pub proof ck : RSL.Bytes)
 (proofLength : proof.length=57607) (checkpointLength : ck.length=1768)
 (publicLength : pub.length≤1880)
 (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest d) hash H)
 (env : RSL.Env) (events : List RSL.Event)
 (observed : w H d hash world render pub proof ck env ⟨.ret (.ok ()),events⟩) :
 NLW_ReaderHeader.decode (NNC_ByteCarriers.protocol ck)=
 some (H (NNC_ByteCarriers.protocol proof),H (NNC_ByteCarriers.protocol pub)) := by
 obtain ⟨pu,pr,cp,hpu,hpr,hcp,outcome,es,native,output⟩:=observed
 have accepted : exit H _ outcome=.ret (.ok ()) := (congrArg RSL.Obs.exit output).symm
 obtain ⟨records,rfl⟩:=exit_ok H _ outcome accepted
 have puLen : pu.val.length≤1880 := by simpa only [←hpu,NNC_ByteCarriers.host,List.length_map] using publicLength
 have prLen : pr.val.length=57607 := by simpa only [←hpr,NNC_ByteCarriers.host,List.length_map] using proofLength
 have cpLen : cp.val.length=1768 := by simpa only [←hcp,NNC_ByteCarriers.host,List.length_map] using checkpointLength
 have header:=NNC_064Weak.accepted_header H ⟨⟨d,pu,pr,cp,hash⟩,world⟩
  ⟨prLen,cpLen,puLen⟩ oracle records es native
 rw [←hcp,←hpr,←hpu,NNC_ByteCarriers.protocol_host,NNC_ByteCarriers.protocol_host,
  NNC_ByteCarriers.protocol_host]
 exact header
#print w
#print axioms contains_native
#print axioms exit_ok
#print axioms accepted_header
end NNC_WeakSpec
