import NJP_CohortNode
import NJP_LoopModel
import MultiproofConePhysicalLevels
import NJE_ParentPackets

set_option autoImplicit false
noncomputable section
namespace NJP_CohortRowLoop
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier NJP_CohortWrite
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Total child interpretation, fixed from the caller's actual oracle. -/
def digest (H : Slice (Slice U8) → RefDigest) : aspis_core.digest.Digest32 Unit where
 coremarkerCopyInst := { cloneInst := { clone := fun x => ok x } }
 digest := fun _ q => ok (H q)

def projectLevel : reference.Level → NJP_LoopModel.Level
 | .Stop s => .stop (raw s)
 | .Done s => .done (raw s)

theorem rows (H : Slice (Slice U8) → RefDigest) (fuel : Nat)
    (s : reference.Scratch) (physical : Slice U8) (i w : Usize)
    (domain : AspisR1.MultiproofConeNodeDomain.RowDomain physical s i w) :
 let typed := eval H (AspisR1.MultiproofConePhysicalLevels.rows fuel s physical i w)
 (typed.1,mapResult projectLevel typed.2)=
 eval H (NJP_RequestTransport.transport
   (NJP_LoopModel.rows (fun n => physical.val[n]!) physical.val.length fuel (raw s) i.val w.val)) := by
 induction fuel generalizing s i w with
 | zero =>
   by_cases halt : i≥s.n
   · have halted : (raw s).n ≤ i.val := halt
     simp only [AspisR1.MultiproofConePhysicalLevels.rows,NJP_LoopModel.rows,if_pos halt,
       if_pos halted,NJP_RequestTransport.transport,eval,mapResult,projectLevel,raw]
   · have halted : ¬ ((raw s).n ≤ i.val) := halt
     simp only [AspisR1.MultiproofConePhysicalLevels.rows,NJP_LoopModel.rows,if_neg halt,
       if_neg halted,NJP_RequestTransport.transport,eval,mapResult]
 | succ fuel ih =>
   by_cases halt : i≥s.n
   · have halted : (raw s).n ≤ i.val := halt
     simp only [AspisR1.MultiproofConePhysicalLevels.rows,NJP_LoopModel.rows,if_pos halt,
       if_pos halted,NJP_RequestTransport.transport,eval,mapResult,projectLevel,raw]
   · have active : i.val < s.n.val := by change ¬ (s.n.val ≤ i.val) at halt;omega
     have halted : ¬ ((raw s).n ≤ i.val) := halt
     have nodeObs := NJP_CohortNode.observation H s physical i w domain active
     obtain ⟨out,result,progress⟩ := AspisR1.MultiproofConeNodeDomain.binary_step_progress
       (digest H) () (fun q => ⟨H q,rfl⟩) physical s i w domain active
     have nodeResult : (eval H (AspisR1.MultiproofConePhysicalProgram.node s physical i w)).2=ok out :=
       (AspisR1.MultiproofConePhysicalProgram.node_result (digest H) () H (fun _ => rfl) s physical i w).trans result
     rw [NJP_RequestTransport.observation] at nodeObs
     dsimp only at nodeObs
     rw [nodeResult] at nodeObs
     have rawResult := congrArg Prod.snd nodeObs
     have rawHistory := congrArg Prod.fst nodeObs
     simp only [mapResult] at rawResult
     simp only [AspisR1.MultiproofConePhysicalLevels.rows,if_neg halt,
       AspisR1.MultiproofConePhysicalLevels.bindRun,eval_bind,nodeResult,
       AspisR1.MultiproofConePhysicalProgram.checked]
     rw [NJP_RequestTransport.observation]
     simp only [NJP_LoopModel.rows,if_neg halted,NJP_LoopModel.bindRun,eval_bind,←rawResult]
     cases out with
     | Stop stopped =>
       simp only [projectRow,projectLevel,eval,List.append_nil,mapResult]
       exact Prod.ext rawHistory rfl
     | Next after ni nw =>
       simp only [projectRow]
       have recurse := ih after ni nw progress.2.1
       rw [NJP_RequestTransport.observation] at recurse
       dsimp only at recurse
       rw [List.map_append,←congrArg Prod.fst recurse,←congrArg Prod.snd recurse,←rawHistory]
       rfl

#print rows
#print axioms rows
end NJP_CohortRowLoop
end
