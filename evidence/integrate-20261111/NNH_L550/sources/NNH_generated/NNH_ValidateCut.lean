import NNH_ValidateEval
import NNH_OptionOk
set_option autoImplicit false
namespace NNH_ValidateCut
open RSL NND_Returned

structure Packet (L : PoolLib) (D : DeployedIds) (v : NND_PoolValues.Values L)
 (a : TX2_242.Args) (env : Env) (out : Validated L) where
 length : a.instruction_data.length=REQUEST_BYTES
 request : L.Request
 decode : L.decodeRequest a.instruction_data=some request
 guards : (decide (L.reqProfile request ≠ PROFILE_BINDING) || decide (L.reqRelease request ≠ RELEASE_BINDING) || decide (L.reqPoolProgram request ≠ D.pool))=false
 lane : UInt8
 lane_ok : L.outputLane (L.reqNullifier request)=some lane
 slot : UInt64
 clock : a.current_slot=.ok slot
 auth : Authenticated
 auth_ok : NNH_AuthEval.value L D ⟨a.verifier_program,a.accounts,L.reqPoolProgram request,lane,slot⟩ env=.ok auth
 proof : OwnedAccount
 head : a.accounts.head?=some proof
 data : Bytes
 data_ok : proof.bytes=.ok data
 scanned : L.Afterstate × Nat
 scan_ok : v.scan data env=.ok scanned
 statement : L.Statement
 reconstruct_ok : v.reconstruct request auth scanned.1 env=.ok statement
 output : out=⟨statement,scanned.2⟩

theorem produce (L : PoolLib) (D : DeployedIds) (v : NND_PoolValues.Values L)
 (a : TX2_242.Args) (env : Env) (out : Validated L)
 (success : NNH_ValidateEval.value L D v a env=.ok out) :
 Nonempty (Packet L D v a env out) := by
 unfold NNH_ValidateEval.value at success
 obtain ⟨len,success⟩ := NNH_ValueOk.seq _ _ out success
 have length : a.instruction_data.length=REQUEST_BYTES := by
  unfold echeck at len
  split at len
  · cases len
  · rename_i h
    simpa only [Bool.not_eq_true,bne_eq_false_iff_eq] using h
 obtain ⟨request,decode,success⟩ := NNH_ValueOk.bind _ _ out success
 obtain ⟨guards,success⟩ := NNH_ValueOk.seq _ _ out success
 have guard_ok : (decide (L.reqProfile request ≠ PROFILE_BINDING) || decide (L.reqRelease request ≠ RELEASE_BINDING) || decide (L.reqPoolProgram request ≠ D.pool))=false := by
  unfold echeck at guards
  split at guards
  · cases guards
  · rename_i h; simpa only [Bool.not_eq_true] using h
 obtain ⟨lane,lane_ok,success⟩ := NNH_ValueOk.bind _ _ out success
 obtain ⟨slot,clock,success⟩ := NNH_ValueOk.bind _ _ out success
 obtain ⟨auth,auth_ok,success⟩ := NNH_ValueOk.bind _ _ out success
 obtain ⟨proof,head,success⟩ := NNH_ValueOk.bind _ _ out success
 obtain ⟨data,data_ok,success⟩ := NNH_ValueOk.bind _ _ out success
 obtain ⟨scanned,scan_ok,success⟩ := NNH_ValueOk.bind _ _ out success
 obtain ⟨statement,reconstruct_ok,success⟩ := NNH_ValueOk.bind _ _ out success
 exact ⟨⟨length,request,NNH_OptionOk.value _ _ _ decode,guard_ok,lane,NNH_OptionOk.value _ _ _ lane_ok,slot,clock,auth,auth_ok,proof,NNH_OptionOk.value _ _ _ head,data,data_ok,scanned,scan_ok,statement,reconstruct_ok,(Except.ok.inj success).symm⟩⟩
#print axioms produce
end NNH_ValidateCut
