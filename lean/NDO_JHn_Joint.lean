import NDO_JHn_TX1Frontier
import NDO_JHk_JointSkeleton
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHn_Joint
open Aeneas Aeneas.Std Result
/-- Exact TX1 goal, still pending final checked application of the byte proof. -/
def Accepted1SavedStatement : Prop := JHk_JointSkeleton.Accepted1SavedStatement
/-- Same corrected world, SDK, TX2 input and slot, and exact TX2 accepted2.
This target omits the three byte-digest equations. Its checked assembly
lemma still takes the separately proved ByteIdentity interface explicitly. -/
def JointStatement : Prop :=
  ∀ [trees : JHe_SHARealization]
    (base : AdapterRw.Ops) (stage : VTop_Stages.Ops)
    (data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (accepted2 : S2W_D189Wrappers.second (JHe_Natives.second base stage)
      CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier data2 slot ()=
        ok (.Ok (JHg_World.e2.heap,()))),
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first (JHe_Natives.first base stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHk_WorldFirst.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 ∧
      S2W_D189Wrappers.second (JHe_Natives.second base stage)
        CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier data2 slot ()=
          ok (.Ok (JHg_World.e2.heap,()))

theorem assembleAccepted (identify : JHn_TX1Frontier.ByteIdentity) : Accepted1SavedStatement := by
  intro trees base stage
  exact JHn_TX1Frontier.of_byte_identity base stage identify
#print axioms assembleAccepted

theorem assembleJoint (identify : JHn_TX1Frontier.ByteIdentity) : JointStatement := by
  intro trees base stage data2 slot accepted2
  obtain ⟨saved,first,identity,length⟩ := JHn_TX1Frontier.corrected_of_byte_identity base stage identify
  exact ⟨saved,first,identity,length,accepted2⟩
#print axioms assembleJoint

/-- The same generic assembly for the predecessor two-class skeleton. -/
theorem retained (identify : JHn_TX1Frontier.ByteIdentity) : JHk_JointSkeleton.JointStatement := by
  intro trees bytes base stage data2 slot accepted2
  exact assembleJoint identify base stage data2 slot accepted2
#print axioms retained
#print JointStatement
end AspisR1.JHn_Joint
end
