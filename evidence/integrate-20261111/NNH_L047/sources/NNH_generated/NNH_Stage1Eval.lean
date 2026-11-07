import NNH_ReturnedClone
import NNH_Tx1ReturnedValues
set_option autoImplicit false
namespace NNH_Stage1Eval
open RSL RSL.TX1_345 NND_Returned
def bodyValue (V : VLib) (P : PreparedNew V) (F : NNH_Tx1ReturnedValues.Values V P) (C : S1Lib V) (a : Args) (p pub ck : OwnedAccount) (env : Env) :
    Except ProgramError Bytes :=
  eseq (id (requireDistinct [p, pub, ck])) <|
  eseq (id (readonlyBuffer p)) <|
  eseq (id (readonlyBuffer pub)) <|
  eseq (id (NNH_ReturnedClone.checkpointValue ck a.program_id true)) <|
  ebind (id ck.bytes) fun checkpointData =>
  eseq (id (requireZero checkpointData)) <|
  ebind (id pub.bytes) fun publicData =>
  eseq (Except.ok ()) <|
  ebind (option (C.decodeStatement publicData) .invalidAccountData) fun st =>
  eseq (Except.ok ()) <|
  eseq (echeck (!C.validateStatement st) .invalidAccountData) <|
  ebind (option (C.encodeCandidate st) .invalidAccountData) fun candidate =>
  ebind (id p.bytes) fun proofData =>
  eseq (echeck (proofData.length != PROOF_ACCOUNT_BYTES
                    || proofData.take AFTERSTATE_BYTES != candidate
                    || proofData.getD (AFTERSTATE_BYTES + 8) 0 != S2_TAG) .invalidAccountData) <|
  ebind (NNH_Tx1ReturnedValues.mapVErrValue V (F.tx1
            ⟨C.semanticPublic st, publicData, slice proofData AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES,
             (a.data.getD 1 0).toNat⟩ env)) fun checkpoint =>
  eseq (echeck (checkpoint.length != checkpointData.length) .invalidAccountData) <|
  Except.ok checkpoint

syntax "nnh_stage1_steps " term : tactic
macro_rules
| `(tactic| nnh_stage1_steps $env:term) => `(tactic|
 first
 | exact NNH_Tx1ReturnedValues.first_returned _ _ _ _ $env
 | exact NNH_ReturnedClone.ofCloned $env _
 | exact NNH_ReturnedClone.checkpoint_returned $env _ _ _
 | exact NND_Returned.rs_lift _ $env () (NNH_ReturnedClone.allocIf $env _)
 | exact NND_Returned.ofExcept $env _
 | exact NND_Returned.ofOption $env _ _
 | exact NND_Returned.check $env _ _
 | exact NND_Returned.rs_lift _ $env () (NND_Returned.alloc $env)
 | exact NND_Returned.rs_pure $env _
 | (apply NND_Returned.seq <;> nnh_stage1_steps $env)
 | (apply NND_Returned.rs_bind <;> nnh_stage1_steps $env)
 | (intro; nnh_stage1_steps $env))

theorem body_returned (V : VLib) (P : PreparedNew V) (F : NNH_Tx1ReturnedValues.Values V P)
 (C : S1Lib V) (a : Args) (p pub ck : OwnedAccount) (env : Env) :
 Returns (body V P C a p pub ck) env (bodyValue V P F C a p pub ck env) := by
 unfold body bodyValue
 nnh_stage1_steps env

#print axioms body_returned
end NNH_Stage1Eval
