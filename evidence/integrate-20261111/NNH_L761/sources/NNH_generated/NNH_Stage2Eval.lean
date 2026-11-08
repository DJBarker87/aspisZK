import NNH_ReturnedClone
import NNH_ValidateEval
import NNH_Tx2CallReturned
set_option autoImplicit false
namespace NNH_Stage2Eval
open RSL RSL.TX2_241 NND_Returned
def value (L : PoolLib) (D : DeployedIds) (V : V2Lib) (v : NND_PoolValues.Values L) (w : NNH_Tx2Values.Values V) (a : Args) (env : Env) : Except ProgramError Unit :=
  eseq (echeck (a.accounts.length != 7 || decide (a.data.length < 4)
                    || a.data.take 4 != REQUEST_MAGIC) .invalidInstructionData) <|
  ebind (NNH_ValidateEval.value L D v ⟨a.program_id, a.accounts, a.data, a.current_slot⟩ env) fun validated =>
  ebind (indexValue a.accounts 0) fun acc0 =>
  ebind (id acc0.bytes) fun proofData =>
  ebind (indexValue a.accounts 6) fun acc6 =>
  ebind (id acc6.bytes) fun checkpointData =>
  eseq (echeck (decide (USIZE_LIMIT ≤ AFTERSTATE_BYTES + validated.proof_length))
            .invalidAccountData) <|
  let proofEnd := AFTERSTATE_BYTES + validated.proof_length
  eseq (echeck (proofData.length != proofEnd) .invalidAccountData) <|
  ebind (Except.ok (v.encode validated.statement env)) fun enc =>
  ebind (option enc .invalidInstructionData) fun publicBytes =>
  eseq (echeck (publicBytes.length != STATEMENT_BYTES) .invalidInstructionData) <|
  ebind (Except.ok (w.auth publicBytes (slice proofData AFTERSTATE_BYTES proofEnd) checkpointData env)) fun r =>
  eseq (NNH_Tx2Values.mapError r) <|
  v.emit validated.statement env

theorem returned (L : PoolLib) (D : DeployedIds) (V : V2Lib)
 (v : NND_PoolValues.Values L) (w : NNH_Tx2Values.Values V) (a : Args) (env : Env) :
 Returns (Ref L D V a) env (value L D V v w a env) := by
 unfold Ref value
 apply seq _ _ env _ _ (check env _ _)
 apply rs_bind _ _ env _ _ (call _ _ _ env _ (NNH_ValidateEval.returned L D v _ env))
 intro validated
 apply rs_bind _ _ env _ _ (index env _ _)
 intro acc0
 apply rs_bind _ _ env _ _ (by first | exact NNH_ReturnedClone.ofCloned env _ | exact NNH_ReturnedClone.checkpoint_returned env _ _ _ | exact ofExcept env _)
 intro proofData
 apply rs_bind _ _ env _ _ (index env _ _)
 intro acc6
 apply rs_bind _ _ env _ _ (by first | exact NNH_ReturnedClone.ofCloned env _ | exact NNH_ReturnedClone.checkpoint_returned env _ _ _ | exact ofExcept env _)
 intro checkpointData
 apply seq _ _ env _ _ (check env _ _)
 apply seq _ _ env _ _ (check env _ _)
 apply rs_bind _ _ env _ _ (rs_lift _ env _ (v.encode_ret _ env))
 intro enc
 apply rs_bind _ _ env _ _ (ofOption env _ _)
 intro publicBytes
 apply seq _ _ env _ _ (check env _ _)
 apply rs_bind _ _ env _ _ (NNH_Tx2Values.call_returned V w _ _ _ env)
 intro r
 apply seq _ _ env _ _ (NNH_Tx2Values.mapVErr_returned V r env)
 exact v.emit_ret _ env

#print axioms returned
end NNH_Stage2Eval
