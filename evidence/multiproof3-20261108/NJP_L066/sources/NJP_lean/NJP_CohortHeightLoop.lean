import NJP_CohortRowLoop

set_option autoImplicit false
noncomputable section
namespace NJP_CohortHeightLoop
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier NJP_CohortWrite NJP_CohortRowLoop
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem level (H : Slice (Slice U8) → RefDigest) (s : reference.Scratch) (physical : Slice U8)
    (domain : AspisR1.MultiproofConeLevelIteration.Domain physical s) :
 let typed := eval H (AspisR1.MultiproofConePhysicalLevels.level s physical)
 (typed.1,mapResult projectLevel typed.2)=
 eval H (NJP_RequestTransport.transport
   (NJP_LoopModel.level (fun n => physical.val[n]!) physical.val.length (raw s))) := by
 exact rows H s.n.val s physical 0#usize 0#usize
   ⟨domain.1,domain.2.1,by simp,by simp,domain.2.2⟩

theorem levels (H : Slice (Slice U8) → RefDigest) (height : Nat)
    (s : reference.Scratch) (physical : Slice U8)
    (domain : AspisR1.MultiproofConeLevelIteration.Domain physical s) :
 let typed := eval H (AspisR1.MultiproofConePhysicalLevels.levels height s physical)
 (typed.1,mapResult projectLevel typed.2)=
 eval H (NJP_RequestTransport.transport
   (NJP_LoopModel.levels (fun n => physical.val[n]!) physical.val.length height (raw s))) := by
 induction height generalizing s with
 | zero => rfl
 | succ height ih =>
   have levelObs := level H s physical domain
   rw [NJP_RequestTransport.observation] at levelObs
   dsimp only at levelObs
   have returned := AspisR1.MultiproofConePhysicalLevels.level_result (digest H) () H
     (fun _ => rfl) s physical domain
   simp only [AspisR1.MultiproofConePhysicalLevels.levels,
     AspisR1.MultiproofConePhysicalLevels.bindRun,eval_bind,returned]
   rw [NJP_RequestTransport.observation]
   simp only [NJP_LoopModel.levels,NJP_LoopModel.bindRun,eval_bind]
   rw [returned] at levelObs
   have rawResult := congrArg Prod.snd levelObs
   have rawHistory := congrArg Prod.fst levelObs
   simp only [Prod.fst,Prod.snd] at rawResult rawHistory
   rw [←rawResult]
   cases result : reference.level_rows (digest H) () s physical 0#usize 0#usize with
   | fail e =>
     simp only [mapResult,AspisR1.MultiproofConePhysicalProgram.checked,eval,List.append_nil]
     exact Prod.ext rawHistory rfl
   | div =>
     simp only [mapResult,AspisR1.MultiproofConePhysicalProgram.checked,eval,List.append_nil]
     exact Prod.ext rawHistory rfl
   | ok out =>
     simp only [mapResult,AspisR1.MultiproofConePhysicalProgram.checked]
     cases out with
     | Stop stopped =>
       simp only [projectLevel,eval,List.append_nil,mapResult]
       exact Prod.ext rawHistory rfl
     | Done after =>
       simp only [projectLevel]
       have afterDomain := AspisR1.MultiproofConeNodeIteration.level_preserve (digest H) ()
         (fun q => ⟨H q,rfl⟩) physical s after domain result
       have recurse := ih after afterDomain
       rw [NJP_RequestTransport.observation] at recurse
       dsimp only at recurse
       have recurseLog := congrArg Prod.fst recurse
       have recurseResult := congrArg Prod.snd recurse
       simp only [Prod.fst,Prod.snd] at recurseLog recurseResult
       rw [List.map_append,←recurseLog,←recurseResult,←rawHistory]
       rfl

#print level
#print axioms level
#print levels
#print axioms levels
end NJP_CohortHeightLoop
end
