import NDO_JHe_SdkCodec
import NDO_JHe_SdkDistinct
import NDO_JHe_SdkInputGate
import NDO_JHe_SdkCheckpoint
import JGx_SdkConstants
import AdapterRwScalar
import JHe_ProofBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_SdkParent
open Aeneas Aeneas.Std Result S2W_D189Entry
open _root_.AdapterRw
attribute [local irreducible] JHb_World.e1 JHb_Header.account JFx_NativeBytes.publicInput
  JHe_Natives.sdk JHe_Natives.data1

/-- Source-order SDK parent constructor. Only the named actual first_decoded
call remains an input to this helper; the concrete theorem supplies it. -/
theorem source (base : Ops) (stage : VTop_Stages.Ops) (saved : alloc.vec.Vec U8)
    (size : saved.val.length=1768)
    (child : first_decoded (JHe_Natives.sdk base stage)
      (S6N_Getters.publicValue JGx_RealStatement.value) JFx_NativeBytes.publicInput
      JFx_NativeBytes.proof 10#usize=ok (.Ok saved)) :
    JHe_Natives.first base stage CPH_Program.verifier JHb_World.e1.first JHe_Natives.data1=ok (.Ok saved) := by
  have count : Slice.len JHb_World.e1.first=3#usize := rfl
  have rawLength : Slice.len JHb_Header.account=58295#usize := by
    apply UScalar.eq_of_val_eq
    exact JHb_Header.length
  have savedLength : alloc.vec.Vec.len saved=1768#usize := by
    apply UScalar.eq_of_val_eq
    exact size
  have cpLength : Slice.len JHe_SdkReads.checkpoint=1768#usize := by
    apply UScalar.eq_of_val_eq
    exact List.length_replicate
  have proofLength : aspis_r1_cost_probe.compact.PROOF_BYTES=ok 57607#usize := JHe_ProofBytes.proof_bytes
  have checked : Usize.checked_add 688#usize 57607#usize=some 58295#usize :=
    AspisR1.AdapterRw.Scalar.checked_add_eq _ _ _ (by scalar_tac)
  have offset : Usize.wrapping_add 688#usize 8#usize=696#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.wrap_add_value 688#usize 8#usize (by decide)
  have common := (S6N_Getters.complete JGx_RealStatement.value).1
  have semantic := (S6N_Getters.complete JGx_RealStatement.value).2
  have index : Slice.index_usize JHe_Natives.data1 1#usize=ok 10#u8 := by
    unfold JHe_Natives.data1
    rfl
  have cast : UScalar.cast .Usize 10#u8=10#usize := by
    apply UScalar.eq_of_val_eq
    scalar_tac
  have distinct : r1_pool_adapter.owned.require_distinct_accounts (JHe_Natives.sdk base stage)
      (Array.make 3#usize [JHb_World.e1.snapshot 0 58295 58295,
        JHb_World.e1.snapshot 1 1880 1880,JHb_World.e1.snapshot 2 1768 1768])=ok (.Ok ()) :=
    JHe_SdkDistinct.source base stage
  unfold JHe_Natives.first r1_pool_adapter.owned.stage1_owned
  simp only [JHe_SdkInputGate.instruction,bind_tc_ok,if_true,count,bne_self_eq_false,
    Bool.false_eq_true,if_false,(S2W_D189Entry.first_index JHb_World.e1).1,
    (S2W_D189Entry.first_index JHb_World.e1).2.1,(S2W_D189Entry.first_index JHb_World.e1).2.2,
    distinct,core.result.Result.Insts.CoreOpsTry.branch,
    JHc_CorrectedOwnership.readonly_guards.1,JHc_CorrectedOwnership.readonly_guards.2,
    JHe_SdkCheckpoint.source,JHe_SdkReads.checkpoint_read,JHe_SdkCheckpoint.zero,
    JHe_SdkReads.publicInput,JHe_SdkCodec.decoded,JHe_SdkCodec.validated,
    core.result.Result.map_err,common,JHe_SdkCodec.encoded,JHe_SdkReads.proof,
    aspis_r1_cost_probe.verifier.PROOF_BYTES,proofLength,JGx_SdkConstants.proofStart,lift,checked,
    core.option.Option.ok_or,rawLength,JHe_SdkInputGate.headerPrefix,JHe_SdkInputGate.comparison,
    offset,JHe_SdkInputGate.tag,aspis_r1_cost_probe.transport.Variant.tag,
    semantic,JHb_Header.suffix,index,cast,child,savedLength,cpLength]
#print axioms source
end AspisR1.JHe_SdkParent
end
