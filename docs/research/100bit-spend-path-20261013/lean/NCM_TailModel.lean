import NCM_Tail

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_TailModel
open Aeneas Aeneas.Std Result MultiproofConeRef NCE_OpeningCuts
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- The tail observer uses the existing cohort definition, including every
rejecting guard and its actual unchanged or mutated scratch. -/
theorem observation (H : Bytes → State) (parsed : OraclePortCompactDraft.Parsed)
    (batch kind : Nat) (nodes : Slice U8) (s : Carrier) :
    eval H (NCM_Tail.model (OraclePortSelectedDraft.capacity (3*batch+kind))
      (encodeState (OraclePortBatchDraft.committedRoot parsed kind)) nodes s) =
      let out := eval H (MultiproofConeVerifyState.tailState parsed batch kind nodes s.scratch)
      (out.1,(out.2.1,{s with scratch:=out.2.2,log:=s.log++out.1})) := by
  unfold NCM_Tail.model MultiproofConeVerifyState.tailState
  dsimp only
  have length : (MultiproofConeCanonical.bytesOf nodes.val).length = nodes.val.length := by
    simp only [MultiproofConeCanonical.bytesOf,List.length_map]
  simp only [length]
  split
  · split
    · exact NCM_VerifierState.observation H _ _ (NCM_Tail.resetCursor s)
    · simp only [eval,List.append_nil]
  · simp only [eval,List.append_nil]

#print axioms observation
end AspisR1.NCM_TailModel
end
