import JHn_R_JHh_C_TX1Candidate
import JHn_R_JHh_ChildBridge
import JHn_ExactReturned
import JHk_WorldFirst
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHn_TX1
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
variable [trees : JHe_SHARealization]
/-- The actual candidate, decoded SDK child, and exact bytes share one output.
Only the453 concrete tree digest equations remain a hypothesis. -/
theorem witness (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    ∃ saved : alloc.vec.Vec U8,
      verifier.candidate.tx1 installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=ok (.Ok saved) ∧
      AdapterRw.first_decoded (JHe_Natives.sdk base stage)
        (S6N_Getters.publicValue JGx_RealStatement.value) JFx_NativeBytes.publicInput
        JFx_NativeBytes.proof 10#usize=ok (.Ok saved) ∧
      saved.val.length=1768 ∧ saved.val=JFx_NativeBytes.checkpoint.val := by
  obtain ⟨p,scratch,initial,out,pending,after,g,flushed,saved,
    prepare,batch,query,flush,write,returned,length,variant,next,size⟩ := JHh_C_TX1Candidate.returns
  exact ⟨saved,returned,JHh_ChildBridge.source base stage saved returned,length,
    JHn_ExactReturned.source saved returned⟩
#print axioms witness

/-- Actual first wrapper acceptance and saved bytes, conditional ONLY on
JHe_SHARealization. Neither acceptance nor body identity is an input law. -/
theorem accepted1_saved (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first (JHe_Natives.first base stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 := by
  obtain ⟨saved,returned,child,length,identity⟩ := witness base stage
  exact ⟨saved,JHe_WrapperReady.source base stage saved length
    (JHe_SdkParent.source base stage saved length child),identity,length⟩
#print axioms accepted1_saved

/-- SAME installed SDK and output on the corrected joint world's TX1 heap. -/
theorem corrected (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first (JHe_Natives.first base stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHk_WorldFirst.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 := by
  obtain ⟨saved,returned,child,length,identity⟩ := witness base stage
  exact ⟨saved,JHk_WorldFirst.source base stage saved length child,identity,length⟩
#print axioms corrected
end AspisR1.JHn_TX1
end
