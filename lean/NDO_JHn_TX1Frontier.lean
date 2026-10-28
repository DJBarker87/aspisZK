import NDO_JHn_R_JHh_C_TX1Candidate
import NDO_JHn_R_JHh_ChildBridge
import NDO_JHk_WorldFirst
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHn_TX1Frontier
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
/-- Exact independently proved interface, retained explicitly here because the
full import union exceeds-M7000. JHn_ExactReturned.source proves this formula;
this module does not import that numerical-proof environment. -/
def ByteIdentity : Prop := ∀ saved : alloc.vec.Vec U8,
  verifier.candidate.tx1 installed digest (toCurrentPublic JFs_PublicSerialization.value)
    JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=ok (.Ok saved) →
  saved.val=JFx_NativeBytes.checkpoint.val
variable [trees : JHe_SHARealization]
/-- The actual candidate and decoded SDK child share one output of length1768.
Only the453 concrete tree digest equations remain a hypothesis; byte identity
is supplied separately to the assembly lemmas below. -/
theorem witness (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    ∃ saved : alloc.vec.Vec U8,
      verifier.candidate.tx1 installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=ok (.Ok saved) ∧
      AdapterRw.first_decoded (JHe_Natives.sdk base stage)
        (S6N_Getters.publicValue JGx_RealStatement.value) JFx_NativeBytes.publicInput
        JFx_NativeBytes.proof 10#usize=ok (.Ok saved) ∧
      saved.val.length=1768 := by
  obtain ⟨p,scratch,initial,out,pending,after,g,flushed,saved,
    prepare,batch,query,flush,write,returned,length,variant,next,size⟩ := JHh_C_TX1Candidate.returns
  exact ⟨saved,returned,JHh_ChildBridge.source base stage saved returned,length⟩
#print axioms witness

/-- Actual wrapper acceptance on the source-selected output, with no byte law. -/
theorem accepted1_exists (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first (JHe_Natives.first base stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧ saved.val.length=1768 := by
  obtain ⟨saved,returned,child,length⟩ := witness base stage
  exact ⟨saved,JHe_WrapperReady.source base stage saved length
    (JHe_SdkParent.source base stage saved length child),length⟩
#print axioms accepted1_exists

/-- Generic assembly frontier. The byte implication is explicit here and is
proved independently by JHn_ExactReturned.source; its application remains an
uncompiled final aggregation, not a discharged headline hypothesis. -/
theorem of_byte_identity (base : AdapterRw.Ops) (stage : VTop_Stages.Ops)
    (identify : ByteIdentity) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first (JHe_Natives.first base stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 := by
  obtain ⟨saved,returned,child,length⟩ := witness base stage
  exact ⟨saved,JHe_WrapperReady.source base stage saved length
    (JHe_SdkParent.source base stage saved length child),identify saved returned,length⟩
#print axioms of_byte_identity

/-- SAME installed SDK and output on the corrected joint world's TX1 heap. -/
theorem corrected_of_byte_identity (base : AdapterRw.Ops) (stage : VTop_Stages.Ops)
    (identify : ByteIdentity) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first (JHe_Natives.first base stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHk_WorldFirst.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 := by
  obtain ⟨saved,returned,child,length⟩ := witness base stage
  exact ⟨saved,JHk_WorldFirst.source base stage saved length child,identify saved returned,length⟩
#print axioms corrected_of_byte_identity
end AspisR1.JHn_TX1Frontier
end
