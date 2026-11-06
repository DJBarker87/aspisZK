import NJP_CohortHeightLoop
import NJP_CohortTerminal
import NJP_LevelsTotal
import MultiproofConeVerifyState

set_option autoImplicit false
noncomputable section
namespace NJP_CohortReturning
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier NJP_CohortWrite NJP_CohortRowLoop
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def finish (root : RefDigest) (physical : Slice U8) : reference.Level → Bool × reference.Scratch
 | .Stop s => (false,s)
 | .Done s => (AspisR1.MultiproofConeRootGuard.sourceRoot root physical s,s)

def answer (out : Bool × reference.Scratch) : Bool × NJP_RowModel.Scratch := (out.1,raw out.2)

theorem finish_same (root : RefDigest) (physical : Slice U8) (out : reference.Level) :
 answer (finish root physical out)=NJP_LoopModel.finish (decode root) physical.val.length (projectLevel out) := by
 cases out with
 | Stop s => rfl
 | Done s => simp only [finish,answer,projectLevel,NJP_LoopModel.finish,NJP_CohortTerminal.same]

def run (root : RefDigest) (physical : Slice U8) (s : reference.Scratch) :=
 AspisR1.MultiproofConePhysicalLevels.bindRun
   (AspisR1.MultiproofConePhysicalLevels.levels 18 {s with «at»:=0#usize} physical)
   fun out => .done (ok (finish root physical out))

theorem observation (H : Slice (Slice U8) → RefDigest) (root : RefDigest)
    (physical : Slice U8) (s : reference.Scratch) (positive : 0<s.n.val) (size : s.n.val≤16) :
 let typed := eval H (run root physical s)
 (typed.1,mapResult answer typed.2)=
 eval H (NJP_RequestTransport.transport
   (NJP_LoopModel.run (decode root) (fun n => physical.val[n]!) physical.val.length (raw s))) := by
 have domain : AspisR1.MultiproofConeLevelIteration.Domain physical {s with «at»:=0#usize} :=
   ⟨positive,size,by simp⟩
 have levels := NJP_CohortHeightLoop.levels H 18 {s with «at»:=0#usize} physical domain
 rw [NJP_RequestTransport.observation] at levels
 dsimp only at levels
 have logs := congrArg Prod.fst levels
 have returns := congrArg Prod.snd levels
 simp only [Prod.fst,Prod.snd] at logs returns
 dsimp only
 unfold run
 simp only [AspisR1.MultiproofConePhysicalLevels.bindRun,eval_bind]
 rw [NJP_RequestTransport.observation]
 unfold NJP_LoopModel.run
 simp only [NJP_LoopModel.bindRun,eval_bind]
 have initial : raw {s with «at»:=0#usize}={raw s with cursor:=0} := rfl
 rw [initial] at returns logs
 rw [←returns]
 cases result : (eval H (AspisR1.MultiproofConePhysicalLevels.levels 18 {s with «at»:=0#usize} physical)).2 with
 | fail e =>
   simp only [mapResult,AspisR1.MultiproofConePhysicalProgram.checked,eval,List.append_nil]
   exact Prod.ext logs rfl
 | div =>
   simp only [mapResult,AspisR1.MultiproofConePhysicalProgram.checked,eval,List.append_nil]
   exact Prod.ext logs rfl
 | ok out =>
   simp only [mapResult,AspisR1.MultiproofConePhysicalProgram.checked,eval,List.append_nil]
   exact Prod.ext logs (congrArg ok (finish_same root physical out))

#print finish_same
#print axioms finish_same
#print observation
#print axioms observation
end NJP_CohortReturning
end
