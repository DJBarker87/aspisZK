import RSL_TX2_242
import NMS_CloneRef233
set_option autoImplicit false
namespace NMS_CloneRef242
open RSL RSL.TX2_242

/- Canonical RSL reference with explicit general ProgramError clone stops.
Only getter interpretation and recursively corrected child references differ.
No normal result, payload, ordered effect, Box or original input is erased. -/
def Ref (L : PoolLib) (D : DeployedIds) (a : Args) : RS (Validated L) :=
  RS.seq (RS.check (a.instruction_data.length != REQUEST_BYTES) .invalidInstructionData) <|
  RS.bind (RS.ofOption (L.decodeRequest a.instruction_data) .invalidInstructionData) fun q =>
  RS.seq (RS.check (decide (L.reqProfile q ≠ PROFILE_BINDING)
                    || decide (L.reqRelease q ≠ RELEASE_BINDING)
                    || decide (L.reqPoolProgram q ≠ D.pool)) .invalidInstructionData) <|
  let pool := L.reqPoolProgram q
  RS.bind (RS.ofOption (L.outputLane (L.reqNullifier q)) .invalidInstructionData) fun lane =>
  RS.bind (RS.ofExcept a.current_slot) fun slot =>
  RS.bind (Spec.call TX2_233.Domain (NMS_CloneRef233.Ref L D)
            ⟨a.verifier_program, a.accounts, pool, lane, slot⟩) fun auth =>
  RS.bind (RS.ofOption a.accounts.head? .notEnoughAccountKeys) fun proofAccount =>
  RS.bind (NMS_GeneralGetters.data proofAccount) fun pdata =>
  RS.bind (L.scanProof pdata) fun scanned =>
  RS.bind (L.reconstruct q auth scanned.1) fun statement =>
  RS.pure { statement := statement, proof_length := scanned.2 }


end NMS_CloneRef242
