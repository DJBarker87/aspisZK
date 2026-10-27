import JGx_TX2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_JointPair
open Aeneas Aeneas.Std Result DrvC_Installation S2Trust S2W_D189Wrappers

/-- SAME-native/SAME-entry composition interface, conditional on TX1 and
remaining SDK-prefix observations. It is not joint non-vacuity. -/
theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (headerBytes : Array U8 688#usize) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → S2W_D189Entry.Record))
    (accepted1 : S2W_D189Wrappers.first (JGx_Natives.first (JGx_CallerSeed.value c) err)
      CPH_FixtureData.copy CPH_FixtureData.allocator (JFv_World.e1 (JGx_ProofAccount.value headerBytes))
      CPH_Program.verifier data1 ()=ok (.Ok (saved,post1,())))
    (same : saved.val=JFx_NativeBytes.checkpoint.val)
    (magic : JGx_MagicGate.value
      (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)) data2=ok false)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8
      (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err))
      CPH_Program.verifier ((JFv_World.e2 (JGx_ProofAccount.value headerBytes)).second secondSizes) data2 slot=
        ok (.Ok JGx_Validated.value))
    (emitted : (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)).op53
      JGx_RealStatement.value=ok (.Ok ()))
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    S2W_D189Wrappers.first (JGx_Natives.first (JGx_CallerSeed.value c) err)
      CPH_FixtureData.copy CPH_FixtureData.allocator (JFv_World.e1 (JGx_ProofAccount.value headerBytes))
      CPH_Program.verifier data1 ()=ok (.Ok (saved,post1,())) ∧
    saved.val=JFx_NativeBytes.checkpoint.val ∧
    S2W_D189Wrappers.second (JGx_Natives.second (JGx_CallerSeed.value c) err) CPH_FixtureData.allocator
      (JFv_World.e2 (JGx_ProofAccount.value headerBytes)) CPH_Program.verifier data2 slot ()=
        ok (.Ok ((JFv_World.e2 (JGx_ProofAccount.value headerBytes)).heap,())) :=
  ⟨accepted1,same,JGx_TX2.accepted2 c err headerBytes data2 slot magic validation emitted realizes⟩
#print axioms source
end AspisR1.JGx_JointPair
end
