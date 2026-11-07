import NND_Tx1ReturnedValues
set_option autoImplicit false
namespace NND_Stage1Eval
open RSL RSL.TX1_345 NND_Returned
def bodyValue (V : VLib) (P : PreparedNew V) (F : NND_Tx1ReturnedValues.Values V P) (C : S1Lib V) (a : Args) (p pub ck : OwnedAccount) (env : Env) :
    Except ProgramError Bytes :=
  eseq (id (requireDistinct [p, pub, ck])) <|
  eseq (id (readonlyBuffer p)) <|
  eseq (id (readonlyBuffer pub)) <|
  eseq (id (verifierCheckpoint ck a.program_id true)) <|
  ebind (id ck.data) fun checkpointData =>
  eseq (id (requireZero checkpointData)) <|
  ebind (id pub.data) fun publicData =>
  ebind (option (C.decodeStatement publicData) .invalidAccountData) fun st =>
  eseq (Except.ok ()) <|
  eseq (echeck (!C.validateStatement st) .invalidAccountData) <|
  ebind (option (C.encodeCandidate st) .invalidAccountData) fun candidate =>
  ebind (id p.data) fun proofData =>
  eseq (echeck (proofData.length != PROOF_ACCOUNT_BYTES
                    || proofData.take AFTERSTATE_BYTES != candidate
                    || proofData.getD (AFTERSTATE_BYTES + 8) 0 != S2_TAG) .invalidAccountData) <|
  ebind (NND_Tx1ReturnedValues.mapVErrValue V (F.tx1
            ⟨C.semanticPublic st, publicData, slice proofData AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES,
             (a.data.getD 1 0).toNat⟩ env)) fun checkpoint =>
  eseq (echeck (checkpoint.length != checkpointData.length) .invalidAccountData) <|
  Except.ok checkpoint

syntax "stage1_steps " term : tactic
macro_rules
| `(tactic| stage1_steps $env:term) => `(tactic|
 first
 | exact NND_Tx1ReturnedValues.first_returned _ _ _ _ $env
 | exact NND_Returned.ofExcept $env _
 | exact NND_Returned.ofOption $env _ _
 | exact NND_Returned.check $env _ _
 | exact NND_Returned.rs_lift _ $env () (NND_Returned.alloc $env)
 | exact NND_Returned.rs_pure $env _
 | (apply NND_Returned.seq <;> stage1_steps $env)
 | (apply NND_Returned.rs_bind <;> stage1_steps $env)
 | (intro; stage1_steps $env))

theorem body_returned (V : VLib) (P : PreparedNew V) (F : NND_Tx1ReturnedValues.Values V P)
 (C : S1Lib V) (a : Args) (p pub ck : OwnedAccount) (env : Env) :
 Returns (body V P C a p pub ck) env (bodyValue V P F C a p pub ck env) := by
 unfold body bodyValue
 stage1_steps env

#print axioms body_returned
end NND_Stage1Eval
