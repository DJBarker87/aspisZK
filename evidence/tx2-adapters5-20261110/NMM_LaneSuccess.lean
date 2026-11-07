import NMM_LaneSymbolic
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NMM_LaneSuccess
open Aeneas Aeneas.Std Result AspisR1 NKP_LaneCuts
attribute [local instance] Classical.propDecidable

theorem loop (oracle : NMM_LaneSymbolic.PureOracle) (p : NLK_LaneInput.Sized)
 (next : U64) (nodes : Frontier)
 (replies : ∀ level, NMM_LaneSymbolic.raw oracle p level = .Ok (nodes level))
 (guards : ∀ level, NLK_LaneLoop.occupied next level = true ∨ nodes level = NLK_LaneTable.empty level) :
 NKF_LaneTrace.run NLK_LaneTable.empty (NLK_LaneLoop.occupied next)
  (NMM_LaneSymbolic.raw oracle p) NLK_LaneLoop.levels NLK_LaneLoop.zero =
 (.Ok (),nodes,NLK_LaneLoop.levels) := by
 rw [NMM_LaneAcceptance.accepted _ _ _ nodes _ _ (fun level _ => replies level) (fun level _ => guards level)]
 have final : NMM_LaneAcceptance.writeAll nodes NLK_LaneLoop.levels NLK_LaneLoop.zero = nodes := by
  funext level
  apply NMM_LaneAcceptance.writeAll_selected
  · simp [NLK_LaneLoop.levels]
  · simp [NLK_LaneLoop.levels]
 rw [final]

/-- Complete successful transcription, with every guard and reply occurrence
explicit. These are model hypotheses to be discharged by the native components;
this declaration is not an accepted-only row root. -/
theorem body (oracle : NMM_LaneSymbolic.PureOracle) (p : NLK_LaneInput.Sized)
 (f : NLK_LaneHeader.Fields) (root : Node) (nodes : Frontier)
 (header : NLK_LaneHeader.sourcePrefix p = .Ok f)
 (rootReply : oracle 0 (NLK_LaneInput.root p) = .Ok root)
 (frontierReplies : ∀ level, NMM_LaneSymbolic.raw oracle p level = .Ok (nodes level))
 (guards : ∀ level, NLK_LaneLoop.occupied f.next level = true ∨ nodes level = NLK_LaneTable.empty level)
 (terminal : f.next.val=0 → root=NLK_LaneTable.final) :
 NMM_LaneSymbolic.body oracle p =
 .Ok (NKP_LaneCarrier.make f.bump f.master f.lane f.next root nodes) := by
 unfold NMM_LaneSymbolic.body
 rw [header,rootReply,loop oracle p f.next nodes frontierReplies guards]
 have good : ¬ (f.next.val=0 ∧ root≠NLK_LaneTable.final) := by
  intro bad
  exact bad.2 (terminal bad.1)
 simp only [NKP_LaneCompletion.finish,if_neg good]

#print loop
#print axioms loop
#print body
#print axioms body
end NMM_LaneSuccess
