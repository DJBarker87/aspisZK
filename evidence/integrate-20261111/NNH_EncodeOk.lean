import NNH_ValidateSdkPort
import LIBB_PoolEncode
set_option autoImplicit false
noncomputable section
namespace NNH_EncodeOk
open Aeneas Aeneas.Std AspisR1 AdapterRw NNH_Libraries

theorem code (statement : LIBB_PoolCarriers.Statement) (bytes : RSL.Bytes)
 (success : LIBB_PoolEncode.evaluator statement=some bytes) :
 ∃ raw,LIBB_PoolEncode.code statement=.ok (.Ok raw) ∧ LIB_Carriers.bytes raw.to_slice=bytes := by
 unfold LIBB_PoolEncode.evaluator at success
 cases source : LIBB_PoolEncode.code statement with
 | fail e => simp only [source,LIBB_ModelGraph.value,LIBB_PoolEncode.option,LIBB_V1DecoderValues.asOption] at success; cases success
 | div => simp only [source,LIBB_ModelGraph.value,LIBB_PoolEncode.option,LIBB_V1DecoderValues.asOption] at success; cases success
 | ok reply => cases reply with
   | Err e => simp only [source,LIBB_ModelGraph.value,LIBB_PoolEncode.option,LIBB_V1DecoderValues.asOption] at success; cases success
   | Ok raw =>
    simp only [source,LIBB_ModelGraph.value,LIBB_PoolEncode.option,LIBB_V1DecoderValues.asOption,Option.some.injEq] at success
    exact ⟨raw,rfl,success⟩

theorem sdk {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (reserve : NP6_StdModel.Reservation)
 (statement : LIBB_PoolCarriers.Statement) (bytes : RSL.Bytes)
 (success : LIBB_PoolEncode.evaluator statement=some bytes) :
 ∃ raw,(NNH_Tx2Configuration.sdk missing env err reserve).op22 statement=.ok (.Ok raw) ∧ LIB_Carriers.bytes raw.to_slice=bytes := by
 obtain ⟨raw,run,same⟩ := code statement bytes success
 refine ⟨raw,?_,same⟩
 change AspisS6CurrentCodecInstallation.encode statement=_
 unfold AspisS6CurrentCodecInstallation.encode
 change AspisS6OuterNativeOps.resultMap _ (LIBB_PoolEncode.code statement)=_
 rw [run]
 rfl
#print axioms code
#print axioms sdk
end NNH_EncodeOk
