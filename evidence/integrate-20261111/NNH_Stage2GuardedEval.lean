import NNH_Stage2Cut
import NNH_ReturnsBundle
set_option autoImplicit false
noncomputable section
namespace NNH_Stage2GuardedEval
open RSL RSL.TX2_241 NND_Returned NNH_Libraries
attribute [local instance] Classical.propDecidable

/-- Parent admission check only. On an admitted call this uses the canonical
LIBB value and its existing Returns proof, without constructing new leaf Values. -/
def guard (p q r : Bytes) (env : Env) : Except V0.VErr Unit :=
 if Dom064 V0 (p,q,r) then authValues.auth p q r env else .error .Checkpoint

theorem guard_returns (p q r : Bytes) (env : Env) :
 Returns (RS.lift (Spec.call (Dom064 V0) (fun x=>V0.tx2auth x.1 x.2.1 x.2.2) (p,q,r)))
 env (.ok (guard p q r env)) := by
 apply rs_lift
 apply call_domain
 intro domain
 unfold guard
 rw [if_pos domain]
 exact authValues.auth_ret p q r env domain

theorem guard_ok (p q r : Bytes) (env : Env) (ok : guard p q r env=.ok ()) :
 Dom064 V0 (p,q,r) ∧ authValues.auth p q r env=.ok () := by
 unfold guard at ok
 split at ok
 · rename_i domain; exact ⟨domain,ok⟩
 · cases ok

def value (a : Args) (env : Env) : Except ProgramError Unit :=
  eseq (echeck (a.accounts.length != 7 || decide (a.data.length < 4)
                    || a.data.take 4 != REQUEST_MAGIC) .invalidInstructionData) <|
  ebind (NNH_ValidateEval.value L D LIBB_PoolLib.values ⟨a.program_id, a.accounts, a.data, a.current_slot⟩ env) fun validated =>
  ebind (indexValue a.accounts 0) fun acc0 =>
  ebind (id acc0.bytes) fun proofData =>
  ebind (indexValue a.accounts 6) fun acc6 =>
  ebind (id acc6.bytes) fun checkpointData =>
  eseq (echeck (decide (USIZE_LIMIT ≤ AFTERSTATE_BYTES + validated.proof_length))
            .invalidAccountData) <|
  let proofEnd := AFTERSTATE_BYTES + validated.proof_length
  eseq (echeck (proofData.length != proofEnd) .invalidAccountData) <|
  ebind (Except.ok (LIBB_PoolLib.values.encode validated.statement env)) fun enc =>
  ebind (option enc .invalidInstructionData) fun publicBytes =>
  eseq (echeck (publicBytes.length != STATEMENT_BYTES) .invalidInstructionData) <|
  ebind (Except.ok (guard publicBytes (slice proofData AFTERSTATE_BYTES proofEnd) checkpointData env)) fun r =>
  eseq (NNH_Tx2Values.mapError r) <|
  LIBB_PoolLib.values.emit validated.statement env


theorem returned (a : Args) (env : Env) :
 Returns (Ref L D V0 a) env (value a env) := by
 unfold Ref value
 apply seq _ _ env _ _ (check env _ _)
 apply rs_bind _ _ env _ _ (call _ _ _ env _ (NNH_ValidateEval.returned L D LIBB_PoolLib.values _ env))
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
 apply rs_bind _ _ env _ _ (rs_lift _ env _ (LIBB_PoolLib.values.encode_ret _ env))
 intro enc
 apply rs_bind _ _ env _ _ (ofOption env _ _)
 intro publicBytes
 apply seq _ _ env _ _ (check env _ _)
 apply rs_bind _ _ env _ _ (guard_returns _ _ _ env)
 intro r
 apply seq _ _ env _ _ (NNH_Tx2Values.mapVErr_returned V0 r env)
 exact LIBB_PoolLib.values.emit_ret _ env

#print axioms guard_returns
#print axioms guard_ok
#print axioms returned
end NNH_Stage2GuardedEval
