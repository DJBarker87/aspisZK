import NNH_064SourceTotal
import NNH_Libraries
set_option autoImplicit false
noncomputable section
namespace NNH_AuthCodeOk
open Aeneas Aeneas.Std AspisR1 VTop_Stages NNH_Libraries

theorem code (env : RSL.Env) (pub proof ck : Slice U8)
 (success : authValues.auth (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck) env=.ok ()) :
 LIBB_Tx2EnvCode.code env pub proof ck=.ok (.Ok ()) := by
 change LIBB_Tx2Auth.value (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck) env=.ok () at success
 unfold LIBB_Tx2Auth.value at success
 rw [dif_pos ⟨LIB_Bytes.bytes_bound pub,LIB_Bytes.bytes_bound proof,LIB_Bytes.bytes_bound ck⟩,
  LIB_Bytes.from_bytes,LIB_Bytes.from_bytes,LIB_Bytes.from_bytes] at success
 change (match (NNH_064SourceTotal.run env pub proof ck).exit with
  | .ret r => r | _ => .error .Checkpoint)=Except.ok () at success
 rw [(NNH_064SourceTotal.components env pub proof ck).1] at success
 cases source : LIBB_Tx2EnvCode.code env pub proof ck with
 | fail e => simp only [source,NNC_WeakSpec.resultExit] at success; cases success
 | div => simp only [source,NNC_WeakSpec.resultExit] at success; cases success
 | ok reply => cases reply with
   | Err e => simp only [source,NNC_WeakSpec.resultExit] at success; cases success
   | Ok unit => cases unit; exact source

theorem entered (env : RSL.Env) (pub proof ck : Slice U8)
 (success : LIBB_Tx2EnvCode.code env pub proof ck=.ok (.Ok ())) :
 ∃ variant,NLE_ParseInstall.parse proof=.ok (.Ok variant) ∧
 LIBB_Tx2EnvCode.common env pub proof ck=.ok (.Ok ()) := by
 unfold LIBB_Tx2EnvCode.code at success
 cases parse : NLE_ParseInstall.parse proof with
 | fail e => simp only [parse,Aeneas.Std.bind_tc_fail] at success; cases success
 | div => simp only [parse,Aeneas.Std.bind_tc_div] at success; cases success
 | ok reply => cases reply with
   | Err e => simp only [parse,Aeneas.Std.bind_tc_ok] at success; cases success
   | Ok variant => exact ⟨variant,parse,by simpa only [parse,Aeneas.Std.bind_tc_ok] using success⟩
#print axioms code
#print axioms entered
end NNH_AuthCodeOk
