import NMX_R8_ReadsFactor241
import NMX_R8_Encoded241
import NMS_R2N_RSLScalarEq
set_option autoImplicit false
noncomputable section
namespace NMX_R8_Reads241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev L := LIBB_PoolLib.library
abbrev V := LIBB_V2Star.library

theorem full (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (v : r1_pool_adapter.ValidatedAsqa) (proof checkpoint : Slice U8)
 (length : v.proof_length = 57607#usize) :
 Simulates (NMS_R2N_RSLError.reply id)
  (NMX_R8_Factor241.afterReads (NMX_R8_Std241.ops env) (NMX_R8_Children241.grouped choices) v proof checkpoint)
  (NMS_R2Replay241.afterReads L V NMX_R8_RelReplay241.verify (NMX_R5_AfterAuth242.value v)
   (NMS_R2N_RSLScalars.bytes proof) (NMS_R2N_RSLScalars.bytes checkpoint)) := by
 rw [NMX_R8_ReadsFactor241.factor env choices v proof checkpoint length]
 have endpoint : RSL.AFTERSTATE_BYTES + (NMX_R5_AfterAuth242.value v).proof_length = 58295 := by
  change RSL.AFTERSTATE_BYTES + v.proof_length.val = 58295
  rw [length]
  unfold RSL.AFTERSTATE_BYTES
  scalar_tac
 have noOverflow : decide (RSL.TX2_241.USIZE_LIMIT ≤ RSL.AFTERSTATE_BYTES +
  (NMX_R5_AfterAuth242.value v).proof_length) = false := by
  rw [endpoint]
  unfold RSL.TX2_241.USIZE_LIMIT
  decide
 have guard : (Slice.len proof != 58295#usize) =
  ((NMS_R2N_RSLScalars.bytes proof).length != RSL.AFTERSTATE_BYTES + (NMX_R5_AfterAuth242.value v).proof_length) := by
  rw [endpoint,NMS_R2N_RSLScalars.bytes_length,NMS_R2N_RSLScalarEq.scalar_bne,NMX_R2_LengthGuard.value]
  have value : (58295#usize).val = 58295 := by scalar_tac
  rw [value]
  by_cases same : proof.val.length = 58295 <;> simp [same]
 unfold NMS_R2Replay241.afterReads NMX_R8_ReadsFactor241.source
 rw [noOverflow,RSL.RS.check_false,RSL.RS.seq_pure,guard]
 split
 · rename_i reject
   rw [reject,RSL.RS.check_true,RSL.RS.seq_throw]
   exact NMS_R2N_Interpreted.pure _ _
 · rename_i accept
   have falseguard : ((NMS_R2N_RSLScalars.bytes proof).length != RSL.AFTERSTATE_BYTES +
    (NMX_R5_AfterAuth242.value v).proof_length) = false := by
    cases h : ((NMS_R2N_RSLScalars.bytes proof).length != RSL.AFTERSTATE_BYTES +
     (NMX_R5_AfterAuth242.value v).proof_length) <;> simp_all
   rw [falseguard,RSL.RS.check_false,RSL.RS.seq_pure]
   have width : proof.val.length = 58295 := by
    by_contra different
    have mismatch : ((NMS_R2N_RSLScalars.bytes proof).length != RSL.AFTERSTATE_BYTES +
     (NMX_R5_AfterAuth242.value v).proof_length) = true := by
     rw [endpoint,NMS_R2N_RSLScalars.bytes_length]
     simp [different]
    rw [mismatch] at falseguard
    contradiction
   apply NMX_R8_EncoderUse241.full v.statement
   intro pub
   exact NMX_R8_Encoded241.full env choices v proof checkpoint pub length width
#print axioms full
end NMX_R8_Reads241
end
