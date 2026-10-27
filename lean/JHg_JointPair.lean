import JHg_WrapperAfterValidation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHg_JointPair
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers
/-- SAME configuration and bank lineage. Every remaining runtime/validation
conjunct stays explicit; this supplies no independently chosen successful native. -/
theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (post1 : S2Trust.Heap (Nat → S2W_D189Entry.Record))
    (accepted1 : first (JGx_Natives.first (JGx_CallerSeed.value c) err)
      CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1 CPH_Program.verifier data1 ()=
        ok (.Ok (saved,post1,())))
    (same : saved.val=JFx_NativeBytes.checkpoint.val)
    (magic : JGx_MagicGate.value (sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)) data2=ok false)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8
      (sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)) CPH_Program.verifier
      (JHg_World.e2.second secondSizes) data2 slot=ok (.Ok JGx_Validated.value))
    (emitted : (sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)).op53
      JGx_RealStatement.value=ok (.Ok ()))
    (JGz_Realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    first (JGx_Natives.first (JGx_CallerSeed.value c) err)
      CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1 CPH_Program.verifier data1 ()=
        ok (.Ok (saved,post1,())) ∧
    saved.val=JFx_NativeBytes.checkpoint.val ∧
    second (JGx_Natives.second (JGx_CallerSeed.value c) err) CPH_FixtureData.allocator JHg_World.e2
      CPH_Program.verifier data2 slot ()=ok (.Ok (JHg_World.e2.heap,())) :=
  ⟨accepted1,same,JHg_WrapperAfterValidation.source c err data2 slot magic validation emitted JGz_Realizes⟩
#print axioms source
end AspisR1.JHg_JointPair
end
