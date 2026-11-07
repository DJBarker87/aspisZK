import NLV_RowSpec094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_BatchInstall
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Every event's complete original input is the initial input; this is
proved from the SAME next-state chain, not a free per-event frame premise. -/
theorem event_inputs {cfg : NLJ_Tx1.Configuration}
 {h : SdkC_Source.Parts → Result SdkC_Source.Digest} {n : Nat}
 {s last : NLV.State} {out : Result NLJ_Tx1.Out} {log : SdkC_Source.Log}
 {events : List NLV.Event} (cuts : NLV.Invocation cfg h n s out log events last) :
 ∀ e∈events,e.pre.core.input=s.core.input := by
 induction cuts with
 | returned head => intro e member; obtain rfl:=List.mem_singleton.mp member; rfl
 | next head tail ih =>
   intro e member
   rcases List.mem_cons.mp member with same | later
   · cases same; rfl
   · exact (ih e later).trans head.inputs
 | fail head => intro e member; obtain rfl:=List.mem_singleton.mp member; rfl
 | div head => intro e member; obtain rfl:=List.mem_singleton.mp member; rfl
theorem event_extents {cfg : NLJ_Tx1.Configuration} (i : NLJ_Tx1.Input)
 (frame : NLJ_Packets.Frame094) (last : NLV.State) (out : Result NLJ_Tx1.Out)
 (log : SdkC_Source.Log) (events : List NLV.Event)
 (cuts : NLV.Invocation cfg i.hashv 20 (NLV.initial i frame) out log events last)
 (domain : NLV_Interface.CallerDomain i) :
 ∀ e∈events,e.pre.core.input.proof.val.length=57607 ∧
 e.pre.core.input.publicBytes.val.length=1880 := by
 intro e member
 have same : e.pre.core.input=i := event_inputs cuts e member
 rw [same]
 exact domain
#print axioms event_inputs
#print axioms event_extents
/-- SAME event arguments, no substituted Prepared/root. The domain is an OPEN
caller obligation, not an allowed native row-root assumption. Counts≤10 are
already internal to CLOSED081; no extra successful-child premise is added. -/
theorem at_call (H : Bytes → State) (s : NLV.State)
 (g : NLJ_Tx1.Scratch) (p : verifier.Prepared) (a : verifier.Accumulator)
 (root : NLJ_Tx1.Root) (site : s.core.locals=.batch0 g p a root)
 (domain : NLV_Interface.BatchDomain s) :
 ∃ parsed : OraclePortCompactDraft.Parsed,
 parsed.wire=MultiproofConeCanonical.bytesOf s.core.input.proof.val ∧
 NLN.BatchPacket H s.core.input.proof parsed (Tx1Q_Carriers.prepared p) root 0#usize := by
 unfold NLV_Interface.BatchDomain at domain
 rw [site] at domain
 obtain ⟨len,parsed,wire,canonical,roots⟩:=domain
 exact ⟨parsed,wire,NLN_TX1_081.root H s.core.input.proof len parsed wire
  (Tx1Q_Carriers.prepared p) root canonical roots⟩
#print axioms at_call
#print at_call
end AspisR1.NLV_BatchInstall
end
