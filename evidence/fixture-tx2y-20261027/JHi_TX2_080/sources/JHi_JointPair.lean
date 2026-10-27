import JHi_TX2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHi_JointPair
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers
/-- Same configured natives and retained bank lineage; the unproved first
wrapper, its exact saved bytes and actual second validation remain explicit. -/
theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (data1 : Slice U8) (slot : U64) (saved : alloc.vec.Vec U8)
    (post1 : S2Trust.Heap (Nat → S2W_D189Entry.Record))
    (accepted1 : first (JGx_Natives.first (JGx_CallerSeed.value (JHi_TX2.seed c)) err)
      CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1 CPH_Program.verifier data1 ()=
        ok (.Ok (saved,post1,())))
    (same : saved.val=JFx_NativeBytes.checkpoint.val)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8
      (sdk (JHf_Configuration.value c err)) CPH_Program.verifier
      (JHg_World.e2.second secondSizes) JHb_DataRequest.value (.Ok slot)=ok (.Ok JGx_Validated.value))
    (sha : JHi_SHARealization.SHARealization) :
    first (JGx_Natives.first (JGx_CallerSeed.value (JHi_TX2.seed c)) err)
      CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1 CPH_Program.verifier data1 ()=
        ok (.Ok (saved,post1,())) ∧
    saved.val=JFx_NativeBytes.checkpoint.val ∧
    second (JGx_Natives.second (JGx_CallerSeed.value (JHi_TX2.seed c)) err)
      CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier JHb_DataRequest.value (.Ok slot) ()=
        ok (.Ok (JHg_World.e2.heap,())) :=
  ⟨accepted1,same,JHi_TX2.after_validation c err slot validation sha⟩
#print axioms source
end AspisR1.JHi_JointPair
end
