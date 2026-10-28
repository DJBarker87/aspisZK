import JHq_TX1
import JHn_Joint
import JHw_TX2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHw_Joint
open Aeneas Aeneas.Std Result
open JHv_Configuration JHu_FixturePdaRuntime
attribute [local irreducible] JHg_World.e2 JHg_World.e1 JHb_World.e1
  JFx_NativeBytes.checkpoint

/-- One saved vector, the original TX1 result, the corrected joint-world TX1
result, and actual TX2 acceptance on the same installed SDK and saved bytes.
The two heaps remain explicit; no equality of those heaps is asserted. -/
theorem source [trees : JHe_SHARealization]
    (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : FixturePdaRuntime base) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first (JHe_Natives.first (adapter base) stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      S2W_D189Wrappers.first (JHe_Natives.first (adapter base) stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHk_WorldFirst.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 ∧
      S2W_D189Wrappers.second (JHe_Natives.second (adapter base) stage)
        CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
        JHb_DataRequest.value (.Ok slot) ()=ok (.Ok (JHg_World.e2.heap,())) := by
  obtain ⟨saved,first,identity,length⟩ := JHq_TX1.accepted1_saved (adapter base) stage
  obtain ⟨jointSaved,jointFirst,jointIdentity,_,second⟩ :=
    JHn_Joint.assembleJoint JHn_ExactReturned.source (adapter base) stage
      JHb_DataRequest.value (.Ok slot) (JHw_TX2.accepted2 base stage slot runtime)
  have same : jointSaved=saved := Subtype.ext (jointIdentity.trans identity.symm)
  subst jointSaved
  exact ⟨saved,first,jointFirst,identity,length,second⟩
#print axioms source
set_option pp.proofs false in
#print source
end AspisR1.JHw_Joint
end
