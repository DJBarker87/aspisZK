import NNH_Stage2GuardedEval
import NNH_ValidateCut
import NNH_Libraries
set_option autoImplicit false
noncomputable section
namespace NNH_Stage2GuardedCut
open RSL RSL.TX2_241 NND_Returned NNH_Libraries

structure Packet (a : TX2_241.Args) (env : Env) where
 cut : NNH_Stage2Cut.Packet a env
 domain : Dom064 V0 (cut.public_bytes,slice cut.proof_data AFTERSTATE_BYTES (AFTERSTATE_BYTES+cut.validated.proof_length),cut.checkpoint_data)


theorem produce (a : TX2_241.Args) (env : Env)
 (success : NNH_Stage2GuardedEval.value a env=.ok ()) : Nonempty (Packet a env) := by
 unfold NNH_Stage2GuardedEval.value at success
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
 have admitted := NNH_Stage2GuardedEval.guard_ok _ _ _ env ((Except.ok.inj auth_eq).trans auth_same)
 have bound := NNH_Stage2Cut.check_false _ _ end_bound
 have length := NNH_Stage2Cut.check_false _ _ proof_length
 have pub_len := NNH_Stage2Cut.check_false _ _ public_length
 refine ⟨⟨⟨NNH_Stage2Cut.check_false _ _ guards,validated,validate_ok,proof_account,proof_index,proof_data,proof_ok,
  checkpoint_account,checkpoint_index,checkpoint_data,checkpoint_ok,?_,?_,public_bytes,
  NNH_OptionOk.value _ _ _ encode_ok,?_,?_,emit_ok⟩,admitted.1⟩⟩
 · simpa only [decide_eq_false_iff_not,not_le] using bound
 · simpa only [bne_eq_false_iff_eq] using length
 · simpa only [bne_eq_false_iff_eq] using pub_len
 · exact admitted.2
#print axioms produce
end NNH_Stage2GuardedCut
