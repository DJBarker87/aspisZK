import NLV_RowSpec094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_BatchInstall
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
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
