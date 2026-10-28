import NDO_JHh_SHARealization
import NDO_JHk_WorldFirst
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_JointSkeleton
open Aeneas Aeneas.Std Result

/-- The requested SHA-only TX1 goal, recorded as a proposition. This is NOT
a proof of that proposition; the complete body identity remains open. -/
def Accepted1SavedStatement : Prop :=
  ∀ [trees : JHe_SHARealization] (base : AdapterRw.Ops) (stage : VTop_Stages.Ops),
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first (JHe_Natives.first base stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768

/-- Exact pending pair statement on the corrected world and SAME installed
SDK. The two SHA classes contain only concrete digest equations. TX2's
accepted2 is explicit; TX1 success and byte identity are conclusions.
This definition is a type-checked skeleton, NOT an inhabited theorem. -/
def JointStatement : Prop :=
  ∀ [trees : JHe_SHARealization] [bytes : JHh_SHARealization]
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

#print Accepted1SavedStatement
#print JointStatement
#print axioms Accepted1SavedStatement
#print axioms JointStatement
end AspisR1.JHk_JointSkeleton
end
