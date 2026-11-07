import NNH_Stage2Eval
import NNH_ValidateCut
import NNH_Libraries
set_option autoImplicit false
noncomputable section
namespace NNH_Stage2Cut
open RSL RSL.TX2_241 NND_Returned NNH_Libraries

structure Packet (a : TX2_241.Args) (env : Env) where
 guards : (a.accounts.length != 7 || decide (a.data.length < 4) || a.data.take 4 != REQUEST_MAGIC)=false
 validated : TX2_242.Validated L
 validate_ok : NNH_ValidateEval.value L D LIBB_PoolLib.values ⟨a.program_id,a.accounts,a.data,a.current_slot⟩ env=.ok validated
 proof_account : OwnedAccount
 proof_index : indexValue a.accounts 0=.ok proof_account
 proof_data : Bytes
 proof_ok : proof_account.bytes=.ok proof_data
 checkpoint_account : OwnedAccount
 checkpoint_index : indexValue a.accounts 6=.ok checkpoint_account
 checkpoint_data : Bytes
 checkpoint_ok : checkpoint_account.bytes=.ok checkpoint_data
 end_bound : AFTERSTATE_BYTES+validated.proof_length<USIZE_LIMIT
 proof_length : proof_data.length=AFTERSTATE_BYTES+validated.proof_length
 public_bytes : Bytes
 encode_ok : LIBB_PoolEncode.evaluator validated.statement=some public_bytes
 public_length : public_bytes.length=STATEMENT_BYTES
 auth_ok : authValues.auth public_bytes (slice proof_data AFTERSTATE_BYTES (AFTERSTATE_BYTES+validated.proof_length)) checkpoint_data env=.ok ()
 emit_ok : LIBB_PoolEmit.evaluator validated.statement=.ok ()

theorem check_false (b : Bool) (e : ProgramError) (success : echeck b e=.ok ()) : b=false := by
 unfold echeck at success
 split at success
 · cases success
 · rename_i h; simpa only [Bool.not_eq_true] using h

theorem produce (a : TX2_241.Args) (env : Env)
 (success : tx2Value a env=.ok ()) : Nonempty (Packet a env) := by
 unfold tx2Value NNH_Stage2Eval.value at success
 obtain ⟨guards,success⟩ := NNH_ValueOk.seq _ _ () success
 obtain ⟨validated,validate_ok,success⟩ := NNH_ValueOk.bind _ _ () success
 obtain ⟨proof_account,proof_index,success⟩ := NNH_ValueOk.bind _ _ () success
 obtain ⟨proof_data,proof_ok,success⟩ := NNH_ValueOk.bind _ _ () success
 obtain ⟨checkpoint_account,checkpoint_index,success⟩ := NNH_ValueOk.bind _ _ () success
 obtain ⟨checkpoint_data,checkpoint_ok,success⟩ := NNH_ValueOk.bind _ _ () success
 obtain ⟨end_bound,success⟩ := NNH_ValueOk.seq _ _ () success
 obtain ⟨proof_length,success⟩ := NNH_ValueOk.seq _ _ () success
 obtain ⟨encoded,encode,success⟩ := NNH_ValueOk.bind _ _ () success
 have encoded_eq := Except.ok.inj encode
 subst encoded
 obtain ⟨public_bytes,encode_ok,success⟩ := NNH_ValueOk.bind _ _ () success
 obtain ⟨public_length,success⟩ := NNH_ValueOk.seq _ _ () success
 obtain ⟨auth,auth_eq,success⟩ := NNH_ValueOk.bind _ _ () success
 obtain ⟨mapped,emit_ok⟩ := NNH_ValueOk.seq _ _ () success
 have auth_same : auth=.ok () := by
  cases auth with
  | ok unit => cases unit; rfl
  | error e => cases mapped
 have bound := check_false _ _ end_bound
 have length := check_false _ _ proof_length
 have pub_len := check_false _ _ public_length
 refine ⟨⟨check_false _ _ guards,validated,validate_ok,proof_account,proof_index,proof_data,proof_ok,
  checkpoint_account,checkpoint_index,checkpoint_data,checkpoint_ok,?_,?_,public_bytes,
  NNH_OptionOk.value _ _ _ encode_ok,?_,?_,emit_ok⟩⟩
 · simpa only [decide_eq_false_iff_not,not_le] using bound
 · simpa only [bne_eq_false_iff_eq] using length
 · simpa only [bne_eq_false_iff_eq] using pub_len
 · exact (Except.ok.inj auth_eq).trans auth_same
#print axioms check_false
#print axioms produce
end NNH_Stage2Cut
