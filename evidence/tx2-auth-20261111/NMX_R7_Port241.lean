import NMX_R7_Fold241
import NMX_R6_Clone
import LIBB_PoolEmit
set_option autoImplicit false
noncomputable section
namespace NMX_R7_Port241
open RSL RSL.TX2_241 NMX_R6_Observation
abbrev L := LIBB_PoolLib.library
abbrev V := LIBB_V2Star.library
abbrev pure := @NMX_R6_Port242.pure
abbrev fromOption := @NMX_R6_Port242.fromOption

def index (accounts : List OwnedAccount) (i : Nat) : Obs (Except ProgramError OwnedAccount) :=
 match accounts[i]? with | some a => pure (.ok a) | none => ⟨.abort,[]⟩

def encode (s : L.Statement) : Obs (Option Bytes) :=
 NMS_R2N_Interpreted.mapObs LIBB_PoolEncode.option (NMX_R6_Observation.scalar (LIBB_PoolEncode.code s))

def mapError (r : Except V.VErr Unit) : Obs (Except ProgramError Unit) :=
 match r with
 | .ok () => pure (.ok ())
 | .error e => ⟨.ret (.error .invalidInstructionData),[.log ("r1:error:" ++ V.debug e)]⟩

def afterPublic (validated : TX2_242.Validated L) (proofData checkpointData publicBytes : Bytes)
 (env : Env) : Obs (Except ProgramError Unit) :=
 if publicBytes.length != STATEMENT_BYTES then pure (.error .invalidInstructionData) else
 bind (NMX_R7_Verify241.verify (publicBytes,slice proofData AFTERSTATE_BYTES
  (AFTERSTATE_BYTES + validated.proof_length),checkpointData) env) fun result =>
 rsbind (mapError result) fun _ => LIBB_PoolEmit.observation validated.statement

def afterReads (validated : TX2_242.Validated L) (proofData checkpointData : Bytes) (env : Env) :=
 if decide (USIZE_LIMIT ≤ AFTERSTATE_BYTES + validated.proof_length) then pure (.error .invalidAccountData) else
 if proofData.length != AFTERSTATE_BYTES + validated.proof_length then pure (.error .invalidAccountData) else
 bind (encode validated.statement) fun enc =>
 rsbind (fromOption enc .invalidInstructionData) fun publicBytes =>
 afterPublic validated proofData checkpointData publicBytes env

def afterValidate (a : Args) (validated : TX2_242.Validated L) (env : Env) :=
 rsbind (index a.accounts 0) fun acc0 =>
 rsbind (pure acc0.bytes) fun proofData =>
 rsbind (index a.accounts 6) fun acc6 =>
 rsbind (pure acc6.bytes) fun checkpointData =>
 afterReads validated proofData checkpointData env

def stage2 (choices : NMX_R4_Authentication.Choices) (a : Args) (env : Env) : Obs (Except ProgramError Unit) :=
 if a.accounts.length != 7 || decide (a.data.length < 4) || a.data.take 4 != REQUEST_MAGIC then
 pure (.error .invalidInstructionData)
 else rsbind (NMX_R6_Validation.validate choices ⟨a.program_id,a.accounts,a.data,a.current_slot⟩ env)
  (fun validated => afterValidate a validated env)

/-- The following helpers concern concrete std/source observations, with no
successful execution or output-membership hypothesis. -/
theorem index_member (accounts : List OwnedAccount) (i : Nat) (env : Env) :
 RS.index accounts i env (index accounts i) := by
 unfold index RS.index
 cases h : accounts[i]? with
 | some a => rfl
 | none =>
   change Spec.map Except.ok Spec.panic env ⟨.abort,[]⟩
   exact Or.inr (Or.inl ⟨[],rfl,rfl⟩)

theorem encode_member (s : L.Statement) (env : Env) :
 L.encodeStatement s env (encode s) :=
 LIBB_ModelGraph.mapped_member _ _ env _ (NMX_R6_Observation.lift _ env)

theorem error_member (r : Except V.VErr Unit) (env : Env) :
 mapVErr V r env (mapError r) := by
 cases r with
 | ok unit => cases unit; rfl
 | error e => exact (NMS_R2ErrorSource.target_obs V e env _).mpr (Or.inl rfl)

#print axioms index_member
#print axioms encode_member
#print axioms error_member
end NMX_R7_Port241
end
