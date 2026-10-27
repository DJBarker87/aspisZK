import JHe_CurrentWriterImage
import JHe_TX1Frontier
import JHh_C_TX1Candidate
import JHh_ChildBridge
import JHh_ImageBytes

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Child
open Aeneas Aeneas.Std Result
variable [sha : JHe_SHARealization]
theorem source (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    ∃ saved : alloc.vec.Vec U8,
      AdapterRw.first_decoded (JHe_Natives.sdk base stage)
        (S6N_Getters.publicValue JGx_RealStatement.value) JFx_NativeBytes.publicInput
        JFx_NativeBytes.proof 10#usize=ok (.Ok saved) ∧ saved.val.length=1768 := by
  obtain ⟨p,scratch,initial,out,pending,after,g,flushed,saved,
    prepare,batch,query,flush,write,returned,length,variant,next,size⟩ := JHh_C_TX1Candidate.returns
  exact ⟨saved,JHh_ChildBridge.source base stage saved returned,length⟩
#print axioms source
end AspisR1.JHh_C_Child
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_TX1
open Aeneas Aeneas.Std Result
variable [sha : JHe_SHARealization]
/-- Selected by the actual installed child return, never supplied as an input. -/
def saved (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) : alloc.vec.Vec U8 :=
  Classical.choose (JHh_C_Child.source base stage)

theorem saved_length (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    (saved base stage).val.length=1768 :=
  (Classical.choose_spec (JHh_C_Child.source base stage)).2
#print axioms saved_length

/-- Actual accepted1, on the source-selected output. Its equality to the
retained checkpoint is NOT asserted by this theorem. -/
theorem accepted1 (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    S2W_D189Wrappers.first (JHe_Natives.first base stage) CPH_FixtureData.copy CPH_FixtureData.allocator
      JHb_World.e1 CPH_Program.verifier JHe_Natives.data1 ()=
        ok (.Ok (saved base stage,JHe_WrapperReady.post (saved base stage),())) :=
  JHe_TX1Frontier.wrapper_of_child base stage (saved base stage) (saved_length base stage)
    (Classical.choose_spec (JHh_C_Child.source base stage)).1
#print axioms accepted1
#print saved
#check @accepted1
#print accepted1

/-- The installed child and wrapper share exactly the candidate-selected
saved vector. Retained checkpoint identity is a separate remaining gate. -/
theorem accepted1_exists (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    ∃ saved : alloc.vec.Vec U8,
      saved.val.length=1768 ∧
      AdapterRw.first_decoded (JHe_Natives.sdk base stage)
        (S6N_Getters.publicValue JGx_RealStatement.value) JFx_NativeBytes.publicInput
        JFx_NativeBytes.proof 10#usize=ok (.Ok saved) ∧
      S2W_D189Wrappers.first (JHe_Natives.first base stage) CPH_FixtureData.copy CPH_FixtureData.allocator
        JHb_World.e1 CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) := by
  obtain ⟨saved,child,size⟩ := JHh_C_Child.source base stage
  exact ⟨saved,size,child,JHe_TX1Frontier.wrapper_of_child base stage saved size child⟩
#print axioms accepted1_exists
end AspisR1.JHh_TX1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_ActualWitness
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
open JHe_CurrentWriterImage
variable [sha : JHe_SHARealization]
/-- The candidate, actual installed child, actual parent wrapper and checksum
request share one output and the writer's actual constructed body. -/
theorem source (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    ∃ (saved : alloc.vec.Vec U8) (body : Slice U8) (hc : CheckpointBytes5Effect.Digest),
      saved.val.length=1768 ∧
      AdapterRw.first_decoded (JHe_Natives.sdk base stage)
        (S6N_Getters.publicValue JGx_RealStatement.value) JFx_NativeBytes.publicInput
        JFx_NativeBytes.proof 10#usize=ok (.Ok saved) ∧
      S2W_D189Wrappers.first (JHe_Natives.first base stage) CPH_FixtureData.copy CPH_FixtureData.allocator
        JHb_World.e1 CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      body.val.length=1736 ∧
      dictionary.digest () (AspisR1Stage2.WireTx2.checksumParts body)=ok hc ∧
      saved.val=body.val ++ hc.val := by
  obtain ⟨p,scratch,initial,out,pending,after,g,flushed,saved,
    prepare,batch,query,flush,write,returned,length,variant,next,size⟩ := JHh_C_TX1Candidate.returns
  let a : verifier.Accumulator := {out with weights:=⟨flushed.val,flushed.property⟩}
  have asize : (accumulator a).weights.val.length=64 := by
    simpa only [accumulator,a,CheckpointBytes3Namespaces.toAccumulator,
      CheckpointBytes3Namespaces.mapVec,Tx1Q_Carriers.accumulator,Tx1Q_Carriers.vec,List.length_map] using size
  have pvariant : (prepared p).variant=.S2 := by
    change CheckpointBytes3Namespaces.toVariant (Tx1Q_Carriers.variant p.variant)=_
    rw [variant]
    rfl
  obtain ⟨hp,hu,hc,body,hpCall,huCall,bodyCall,hcCall,bodySize,image⟩ :=
    JHe_WriterImage.source dictionary () total (prepared p) (accumulator a)
      JFx_NativeBytes.proof JFx_NativeBytes.publicInput saved.deref asize pvariant next
      (code_run p a saved write)
  have bodyBytes := JHh_ImageBytes.source _ body bodyCall
  have child := JHh_ChildBridge.source base stage saved returned
  exact ⟨saved,body,hc,length,child,
    JHe_TX1Frontier.wrapper_of_child base stage saved length child,
    bodySize,hcCall,by rw [bodyBytes];exact image⟩
#print axioms source

/-- The image/checksum witness belongs to the EXACT output exported by
JHh_TX1.accepted1. Result injectivity avoids evaluating either heap or body. -/
theorem selected (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    ∃ (body : Slice U8) (hc : CheckpointBytes5Effect.Digest),
      (JHh_TX1.saved base stage).val.length=1768 ∧
      body.val.length=1736 ∧
      dictionary.digest () (AspisR1Stage2.WireTx2.checksumParts body)=ok hc ∧
      (JHh_TX1.saved base stage).val=body.val ++ hc.val := by
  obtain ⟨saved,body,hc,length,child,wrapper,bsize,call,image⟩ := source base stage
  have same : saved=JHh_TX1.saved base stage :=
    congrArg Prod.fst (core.result.Result.Ok.inj
      (Result.ok.inj (wrapper.symm.trans (JHh_TX1.accepted1 base stage))))
  rw [same] at length image
  exact ⟨body,hc,length,bsize,call,image⟩
#print axioms selected
#check @selected
end AspisR1.JHh_C_ActualWitness
end
