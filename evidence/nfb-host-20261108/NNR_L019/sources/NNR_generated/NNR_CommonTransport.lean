import NNR_InvocationTransport
import NNR_SeedTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_CommonTransport
open Aeneas Aeneas.Std Result VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NLT_NativeInvocation NNH_NativeOracleSlots

theorem accepted (H : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (k : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)
 {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X)
 (pub proof ck : Slice U8) (len : proof.val.length = 57607)
 (value : core.result.Result Unit verifier.Error) (records : List (Occurrence (part H pda k r) d hash))
 (native : Invocation (part H pda k r) d hash
  (NLT_NativeSource.skeleton (part H pda k r) d pub proof ck hash) (.ok value) records) :
 ∃ records' : List (Occurrence H d hash),
 Invocation H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) (.ok value) records' ∧
 records'.map NLT_NativeInvocation.actual = records.map NLT_NativeInvocation.actual := by
 obtain ⟨rs,transported,equal⟩ := NNR_InvocationTransport.forward H pda k r d hash _ _ records native
  (NNR_RecordTransport.window H pda k r d hash pub proof ck len value records native)
 exact ⟨rs,NLT_ReseedTransport.forward _ _
  (NNR_SeedTransport.source (.Ok ()) (.Ok ()) (NLP_NativeMerkle.action (part H pda k r))
   (NLP_NativeMerkle.action H) (NLB_Parent.finish (.Ok ())) d pub proof ck hash)
  _ rs transported,equal⟩
#print axioms accepted
end AspisR1.NNR_CommonTransport
end
