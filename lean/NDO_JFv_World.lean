import RPz8_CPH_FixtureAdmission
import RPz8_CPH_FixtureGame
import RPz8_JFx_NativeBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_World
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState Hist_RuntimeEntry

def saved : alloc.vec.Vec U8 := ⟨JFx_NativeBytes.checkpoint.val,JFx_NativeBytes.checkpoint.property⟩
def buffer (proofAccount : Slice U8) (n : Nat) : Slice U8 :=
  if n=0 then proofAccount else if n=1 then JFx_NativeBytes.publicInput else CPH_FixtureData.buffer n

def initial (proofAccount : Slice U8) : Bank :=
  ⟨fun n => ⟨CPH_Program.verifier,buffer proofAccount n⟩,fun _ => 1⟩
def final (proofAccount : Slice U8) : Bank := CPR_SourceBank.afterCopy (cached (initial proofAccount)) 2 saved

def observations (proofAccount : Slice U8) : Observations Bool Unit where
  bank := fun t => if t then final proofAccount else initial proofAccount
  layout := fun t => if t then CPH_FixtureData.layout2 else CPH_FixtureData.layout1
  next := fun t u => t=false ∧ u=true
  intervening := fun _ _ => []
  parentReply := fun _ => .ok (.Ok ())
  copied := fun _ => saved
  actions := fun _ => []
  parentTentative := fun t => if t then cached (final proofAccount) else final proofAccount
  physicalEvents := fun _ => []

def e1 (proofAccount : Slice U8) := entry (observations proofAccount) false
def e2 (proofAccount : Slice U8) := entry (observations proofAccount) true

theorem saved_length : saved.val.length=1768 := JFx_NativeBytes.checkpointBytes_length

theorem game (proofAccount : Slice U8) (n1 : S2W_ExtractionBoundary.First)
    (n2 : S2W_ExtractionBoundary.Second) :
    CPH_Game.DeployedPairExecution (observations proofAccount) false true
      (e1 proofAccount) (e2 proofAccount) saved [] n1 n2 CPH_FixtureData.copy
      CPH_FixtureData.allocator CPH_Program.verifier := by
  refine ⟨⟨⟨rfl,rfl⟩,rfl,rfl⟩,⟨rfl,rfl,List.not_mem_nil⟩,rfl,⟨⟨rfl,rfl,?_⟩,?_⟩⟩
  · exact CPG_RuntimeTrace.Executes.nil _
  · exact CPG_RuntimeTrace.Executes.nil _

theorem persistence (proofAccount : Slice U8) (system : S2W_ExtractionBoundary.Program) :
    CPR_DataPersistence.TwoTransactionLaw
      (adjacent (observations proofAccount)) (ordinary (observations proofAccount) system)
      (before (observations proofAccount)) (tentative (observations proofAccount))
      (success (observations proofAccount)) (loaded (observations proofAccount)) := by
  intro t u linked key eligible
  have ht : t=false := linked.1.1
  have hu : u=true := linked.1.2
  subst t;subst u
  rfl

#print axioms saved_length
#print axioms game
#print axioms persistence
end AspisR1.JFv_World
end
