import RSL_TX2_241
import NMS_CloneRef242
set_option autoImplicit false
namespace NMS_CloneRef241
open RSL RSL.TX2_241
open RSL.TX2_241

/- Canonical RSL reference with explicit general ProgramError clone stops.
Only getter interpretation and recursively corrected child references differ.
No normal result, payload, ordered effect, Box or original input is erased. -/
def Ref (L : PoolLib) (D : DeployedIds) (V : V2Lib) (a : Args) : RS Unit :=
  RS.seq (RS.check (a.accounts.length != 7 || decide (a.data.length < 4)
                    || a.data.take 4 != REQUEST_MAGIC) .invalidInstructionData) <|
  RS.bind (Spec.call TX2_242.Domain (NMS_CloneRef242.Ref L D)
            ⟨a.program_id, a.accounts, a.data, a.current_slot⟩) fun validated =>
  RS.bind (RS.index a.accounts 0) fun acc0 =>
  RS.bind (NMS_GeneralGetters.data acc0) fun proofData =>
  RS.bind (RS.index a.accounts 6) fun acc6 =>
  RS.bind (NMS_GeneralGetters.data acc6) fun checkpointData =>
  RS.seq (RS.check (decide (USIZE_LIMIT ≤ AFTERSTATE_BYTES + validated.proof_length))
            .invalidAccountData) <|
  let proofEnd := AFTERSTATE_BYTES + validated.proof_length
  RS.seq (RS.check (proofData.length != proofEnd) .invalidAccountData) <|
  RS.bind (RS.lift (L.encodeStatement validated.statement)) fun enc =>
  RS.bind (RS.ofOption enc .invalidInstructionData) fun publicBytes =>
  RS.seq (RS.check (publicBytes.length != STATEMENT_BYTES) .invalidInstructionData) <|
  RS.bind (RS.lift (Spec.call (Dom064 V) (fun x => V.tx2auth x.1 x.2.1 x.2.2)
            (publicBytes, slice proofData AFTERSTATE_BYTES proofEnd, checkpointData))) fun r =>
  RS.seq (mapVErr V r) <|
  L.emitResult validated.statement


end NMS_CloneRef241
