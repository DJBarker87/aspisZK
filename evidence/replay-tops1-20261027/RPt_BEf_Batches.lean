import RPt_BEf_Pure
import RPz7_SdkC_BatchSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEf_Batches
open Aeneas Aeneas.Std Result SdkC_Source

theorem current {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest)
    (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (source : ∀ parts, D.digest () parts = hashv parts)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared)
    (root : Array U8 32#usize) (state : S) (before : Log) :
    (BEf_Carrier.run call (SdkC_BatchSource.currentCode hashv proof p root) state before).1 =
      Op5T_Install.currentBatch Port4B_Install.leaves D proof p root 0#usize () ∧
    (BEf_Carrier.run call (SdkC_BatchSource.currentCode hashv proof p root) state before).2.2 =
      (SdkC_Source.run hashv (SdkC_BatchSource.currentCode hashv proof p root) before).2 := by
  have same := BEf_Carrier.source call hashv binding
    (SdkC_BatchSource.currentCode hashv proof p root) state before
  exact ⟨(congrArg Prod.fst same).trans
    (SdkC_BatchSource.current_source hashv D source proof p root before),congrArg Prod.snd same⟩

theorem stage {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest)
    (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (source : ∀ parts, D.digest () parts = hashv parts)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared)
    (root : Array U8 32#usize) (state : S) (before : Log) :
    (BEf_Carrier.run call (SdkC_BatchSource.stageCode hashv proof p root) state before).1 =
      Op5T_Install.stageBatch Port4B_Install.leaves D proof p root 1#usize () ∧
    (BEf_Carrier.run call (SdkC_BatchSource.stageCode hashv proof p root) state before).2.2 =
      (SdkC_Source.run hashv (SdkC_BatchSource.stageCode hashv proof p root) before).2 := by
  have same := BEf_Carrier.source call hashv binding
    (SdkC_BatchSource.stageCode hashv proof p root) state before
  exact ⟨(congrArg Prod.fst same).trans
    (SdkC_BatchSource.stage_source hashv D source proof p root before),congrArg Prod.snd same⟩

/-- The source interpreter can use the entire mutable carrier without any
cardinality restriction. These equations describe that interpreter; native
carrier correspondence is deliberately not inferred from its definition. -/
theorem frames {S : Type} (hashv : Parts → Result Digest)
    (proof0 proof1 : Slice U8) (p0 : AspisR1CurrentCaller.verifier.Prepared)
    (p1 : VTop_Stages.verifier.Prepared) (root0 root1 : Array U8 32#usize)
    (state : S) (before : Log) :
    (BEf_Carrier.run (BEf_Pure.call hashv)
      (SdkC_BatchSource.currentCode hashv proof0 p0 root0) state before).2.1 = state ∧
    (BEf_Carrier.run (BEf_Pure.call hashv)
      (SdkC_BatchSource.stageCode hashv proof1 p1 root1) state before).2.1 = state :=
  ⟨BEf_Carrier.frame _ (fun _ _ => rfl) _ _ _,
   BEf_Carrier.frame _ (fun _ _ => rfl) _ _ _⟩

#print axioms current
#print axioms stage
#print axioms frames
end AspisR1.BEf_Batches
end
