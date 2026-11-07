import NNH_ReturnedClone
import NNH_AuthEval
import NND_PoolValues
import RSL_TX2_242
set_option autoImplicit false
namespace NNH_ValidateEval
open RSL RSL.TX2_242 NND_Returned
def value (L : PoolLib) (D : DeployedIds) (v : NND_PoolValues.Values L) (a : Args) (env : Env) : Except ProgramError (Validated L) :=
  eseq (echeck (a.instruction_data.length != REQUEST_BYTES) .invalidInstructionData) <|
  ebind (option (L.decodeRequest a.instruction_data) .invalidInstructionData) fun q =>
  eseq (echeck (decide (L.reqProfile q ≠ PROFILE_BINDING)
                    || decide (L.reqRelease q ≠ RELEASE_BINDING)
                    || decide (L.reqPoolProgram q ≠ D.pool)) .invalidInstructionData) <|
  let pool := L.reqPoolProgram q
  ebind (option (L.outputLane (L.reqNullifier q)) .invalidInstructionData) fun lane =>
  ebind (id a.current_slot) fun slot =>
  ebind (NNH_AuthEval.value L D ⟨a.verifier_program, a.accounts, pool, lane, slot⟩ env) fun auth =>
  ebind (option a.accounts.head? .notEnoughAccountKeys) fun proofAccount =>
  ebind (id proofAccount.bytes) fun pdata =>
  ebind (v.scan pdata env) fun scanned =>
  ebind (v.reconstruct q auth scanned.1 env) fun statement =>
  Except.ok { statement := statement, proof_length := scanned.2 }

theorem returned (L : PoolLib) (D : DeployedIds) (v : NND_PoolValues.Values L) (a : Args) (env : Env) :
 Returns (Ref L D a) env (value L D v a env) := by
 unfold Ref value
 apply seq _ _ env _ _ (check env _ _)
 apply rs_bind _ _ env _ _ (ofOption env _ _)
 intro q
 apply seq _ _ env _ _ (check env _ _)
 apply rs_bind _ _ env _ _ (ofOption env _ _)
 intro lane
 apply rs_bind _ _ env _ _ (by first | exact NNH_ReturnedClone.ofCloned env _ | exact NNH_ReturnedClone.checkpoint_returned env _ _ _ | exact ofExcept env _)
 intro slot
 apply rs_bind _ _ env _ _ (call _ _ _ env _ (NNH_AuthEval.returned L D _ env))
 intro auth
 apply rs_bind _ _ env _ _ (ofOption env _ _)
 intro proofAccount
 apply rs_bind _ _ env _ _ (by first | exact NNH_ReturnedClone.ofCloned env _ | exact NNH_ReturnedClone.checkpoint_returned env _ _ _ | exact ofExcept env _)
 intro pdata
 apply rs_bind _ _ env _ _ (v.scan_ret pdata env)
 intro scanned
 apply rs_bind _ _ env _ _ (v.reconstruct_ret q auth scanned.1 env)
 intro statement
 exact rs_pure env _

#print axioms returned
end NNH_ValidateEval
