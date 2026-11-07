import NNH_ReturnsBundle
import NNH_ValueOk
import NNH_OptionOk
import NNH_Stage2Cut
set_option autoImplicit false
noncomputable section
namespace NNH_Stage1Cut
open RSL RSL.TX1_345 NND_Returned NNH_Libraries

structure Packet (a : Args) (p pub ck : OwnedAccount) (saved : Bytes) (env : Env) where
 distinct : requireDistinct [p,pub,ck]=.ok ()
 proof_readonly : readonlyBuffer p=.ok ()
 public_readonly : readonlyBuffer pub=.ok ()
 checkpoint_owned : NNH_ReturnedClone.checkpointValue ck a.program_id true=.ok ()
 checkpoint_data : Bytes
 checkpoint_read : ck.bytes=.ok checkpoint_data
 checkpoint_zero : requireZero checkpoint_data=.ok ()
 public_data : Bytes
 public_read : pub.bytes=.ok public_data
 statement : C.Statement
 decode : C.decodeStatement public_data=some statement
 valid : C.validateStatement statement=true
 candidate : Bytes
 encode : C.encodeCandidate statement=some candidate
 proof_data : Bytes
 proof_read : p.bytes=.ok proof_data
 proof_guard : (proof_data.length != PROOF_ACCOUNT_BYTES || proof_data.take AFTERSTATE_BYTES != candidate || proof_data.getD (AFTERSTATE_BYTES+8) 0 != S2_TAG)=false
 child : NNH_Tx1ReturnedValues.mapVErrValue VL (NNH_Tx1Returns.values.tx1
  ⟨C.semanticPublic statement,public_data,slice proof_data AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES,(a.data.getD 1 0).toNat⟩ env)=.ok saved
 saved_length : saved.length=checkpoint_data.length

theorem produce (a : Args) (p pub ck : OwnedAccount) (saved : Bytes) (env : Env)
 (success : NNH_Stage1Eval.bodyValue VL P NNH_Tx1Returns.values C a p pub ck env=.ok saved) :
 Nonempty (Packet a p pub ck saved env) := by
 unfold NNH_Stage1Eval.bodyValue at success
 obtain ⟨distinct,success⟩ := NNH_ValueOk.seq _ _ saved success
 obtain ⟨proof_readonly,success⟩ := NNH_ValueOk.seq _ _ saved success
 obtain ⟨public_readonly,success⟩ := NNH_ValueOk.seq _ _ saved success
 obtain ⟨checkpoint_owned,success⟩ := NNH_ValueOk.seq _ _ saved success
 obtain ⟨checkpoint_data,checkpoint_read,success⟩ := NNH_ValueOk.bind _ _ saved success
 obtain ⟨checkpoint_zero,success⟩ := NNH_ValueOk.seq _ _ saved success
 obtain ⟨public_data,public_read,success⟩ := NNH_ValueOk.bind _ _ saved success
 obtain ⟨alloc,success⟩ := NNH_ValueOk.seq _ _ saved success
 obtain ⟨statement,decode,success⟩ := NNH_ValueOk.bind _ _ saved success
 obtain ⟨alloc2,success⟩ := NNH_ValueOk.seq _ _ saved success
 obtain ⟨valid,success⟩ := NNH_ValueOk.seq _ _ saved success
 obtain ⟨candidate,encode,success⟩ := NNH_ValueOk.bind _ _ saved success
 obtain ⟨proof_data,proof_read,success⟩ := NNH_ValueOk.bind _ _ saved success
 obtain ⟨proof_guard,success⟩ := NNH_ValueOk.seq _ _ saved success
 obtain ⟨checkpoint,child,success⟩ := NNH_ValueOk.bind _ _ saved success
 obtain ⟨size,success⟩ := NNH_ValueOk.seq _ _ saved success
 have same := Except.ok.inj success
 subst checkpoint
 have good : C.validateStatement statement=true := by
  have flag := NNH_Stage2Cut.check_false _ _ valid
  simpa only [Bool.not_eq_false] using flag
 have length := NNH_Stage2Cut.check_false _ _ size
 exact ⟨⟨distinct,proof_readonly,public_readonly,checkpoint_owned,checkpoint_data,checkpoint_read,
  checkpoint_zero,public_data,public_read,statement,NNH_OptionOk.value _ _ _ decode,good,
  candidate,NNH_OptionOk.value _ _ _ encode,proof_data,proof_read,
  NNH_Stage2Cut.check_false _ _ proof_guard,child,(bne_eq_false_iff_eq.mp length)⟩⟩
#print axioms produce
end NNH_Stage1Cut
