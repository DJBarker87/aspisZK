import NCM_VerifierProjection

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_VerifierState
open Aeneas Aeneas.Std Result MultiproofConeRef NCE_OpeningCuts NCE_CarrierEffects
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Exact carrier observer for the cohort's existing scratch-returning
verifier. This adds no callee equality hypothesis or alternative execution. -/
theorem observation (H : Bytes → State) (root : NCE_VerifierCuts.Digest)
    (physical : Slice U8) (s : Carrier) :
    eval H (NCM_Verifier.model root physical s) =
      let out := eval H (MultiproofConeVerifyState.verifyState root physical s.scratch)
      (out.1,(out.2.1,{s with scratch:=out.2.2,log:=s.log++out.1})) := by
  unfold NCM_Verifier.model MultiproofConeVerifyState.verifyState
  split
  · simp only [eval_bind,annotate_eval,eval,List.append_nil]
    cases returned : (eval H (MultiproofConePhysicalTransport.transport
      (MultiproofConePhysicalLevels.levels 18 s.scratch physical))).2 with
    | fail e => rfl
    | div => rfl
    | ok out => cases out <;> rfl
  · simp only [eval,List.append_nil]

#print axioms observation
end AspisR1.NCM_VerifierState
end
