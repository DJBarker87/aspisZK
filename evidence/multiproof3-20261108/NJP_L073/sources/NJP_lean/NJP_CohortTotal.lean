import NJP_CohortReturning

set_option autoImplicit false
noncomputable section
namespace NJP_CohortTotal
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier NJP_CohortWrite NJP_CohortRowLoop
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem levels (H : Slice (Slice U8) → RefDigest) (height : Nat)
    (physical : Slice U8) (s : reference.Scratch)
    (domain : AspisR1.MultiproofConeLevelIteration.Domain physical s)
    (bytes : physical.val.length ≤ 9216) :
 ∃ out, (eval H (AspisR1.MultiproofConePhysicalLevels.levels height s physical)).2=ok out := by
 have rawDomain : NJP_LoopTotal.LevelDomain physical.val.length (raw s) :=
   ⟨domain.1,domain.2.1,domain.2.2,bytes⟩
 obtain ⟨rawOut,rawReturned,_⟩ := NJP_LevelsTotal.levels_total
   (NJP_RequestTransport.hash H) (fun n => physical.val[n]!) physical.val.length height (raw s) rawDomain
 have observation := NJP_CohortHeightLoop.levels H height s physical domain
 rw [NJP_RequestTransport.observation] at observation
 have result := congrArg Prod.snd observation
 dsimp only at result
 rw [rawReturned] at result
 cases returned : (eval H (AspisR1.MultiproofConePhysicalLevels.levels height s physical)).2 with
 | fail e =>
   simp only [returned,mapResult] at result
   cases result
 | div =>
   simp only [returned,mapResult] at result
   cases result
 | ok out => exact ⟨out,returned⟩

#print levels
#print axioms levels
end NJP_CohortTotal
end
