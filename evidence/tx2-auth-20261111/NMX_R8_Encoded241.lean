import NMX_R8_ProofSlice241
import NMX_R8_RelReplay241
set_option autoImplicit false
noncomputable section
namespace NMX_R8_Encoded241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev L := LIBB_PoolLib.library
abbrev V := LIBB_V2Star.library

theorem full (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (v : r1_pool_adapter.ValidatedAsqa) (proof checkpoint : Slice U8)
 (pub : Array U8 1880#usize) (length : v.proof_length = 57607#usize)
 (width : proof.val.length = 58295) :
 Simulates (NMS_R2N_RSLError.reply id)
  (NMX_R8_Factor241.afterEncode (NMX_R8_Std241.ops env) (NMX_R8_Children241.grouped choices)
   v proof checkpoint 688#usize 58295#usize pub)
  (NMS_R2Replay241.afterPublic L V NMX_R8_RelReplay241.verify (NMX_R5_AfterAuth242.value v)
   (NMS_R2N_RSLScalars.bytes proof) (NMS_R2N_RSLScalars.bytes checkpoint)
   (NMS_R2N_RSLScalars.bytes pub.to_slice)) := by
 rw [NMX_R8_EncodedFactor241.factor]
 unfold NMX_R8_EncodedFactor241.source
 obtain ⟨selected,run,exactBytes⟩ := NMX_R8_ProofSlice241.selected proof width
 rw [run]
 change Simulates _ (RSL.Spec.bind (RSL.Spec.pure selected) _) _
 rw [RSL.Spec.bind_pure]
 have publicLength := NMS_R2N_RSLRanges.public_extent pub
 have check : ((NMS_R2N_RSLScalars.bytes pub.to_slice).length != RSL.STATEMENT_BYTES) = false := by
  rw [publicLength]; simp
 have endpoint : RSL.AFTERSTATE_BYTES + (NMX_R5_AfterAuth242.value v).proof_length = 58295 := by
  change RSL.AFTERSTATE_BYTES + v.proof_length.val = 58295
  rw [length]
  unfold RSL.AFTERSTATE_BYTES
  scalar_tac
 unfold NMS_R2Replay241.afterPublic
 rw [check,RSL.RS.check_false,RSL.RS.seq_pure,endpoint]
 have h := NMX_R8_VerifierUse241.full v.statement pub.to_slice selected checkpoint
 rw [exactBytes] at h
 exact h
#print axioms full
end NMX_R8_Encoded241
end
