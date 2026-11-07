import NMS_RSLStepFacts
import NMS_RSLDomains
set_option autoImplicit false
namespace NMS_RSL241Replay
open RSL RSL.TX2_241 NMS_RSLRefine
abbrev VerifyArgs := Bytes × Bytes × Bytes
abbrev VerifyNative (V : V2Lib) := VerifyArgs → Env → Obs (Except V.VErr Unit)
/-- Complete 064 law at its original triple, on exactly Dom064 V. -/
def VerifyPacket (V : V2Lib) (native : VerifyNative V) : Prop :=
 ∀ x env, Dom064 V x → V.tx2auth x.1 x.2.1 x.2.2 env (native x env)

def afterPublic (L : PoolLib) (V : V2Lib) (verify : VerifyArgs → Spec (Except V.VErr Unit))
 (validated : TX2_242.Validated L) (proofData checkpointData publicBytes : Bytes) : RS Unit :=
 RS.seq (RS.check (publicBytes.length != STATEMENT_BYTES) .invalidInstructionData) <|
 RS.bind (RS.lift (verify (publicBytes,
   slice proofData AFTERSTATE_BYTES (AFTERSTATE_BYTES + validated.proof_length), checkpointData))) fun r =>
 RS.seq (mapVErr V r) <| L.emitResult validated.statement

def afterReads (L : PoolLib) (V : V2Lib) (verify : VerifyArgs → Spec (Except V.VErr Unit))
 (validated : TX2_242.Validated L) (proofData checkpointData : Bytes) : RS Unit :=
 RS.seq (RS.check (decide (USIZE_LIMIT ≤ AFTERSTATE_BYTES + validated.proof_length))
   .invalidAccountData) <|
 RS.seq (RS.check (proofData.length != AFTERSTATE_BYTES + validated.proof_length)
   .invalidAccountData) <|
 RS.bind (RS.lift (L.encodeStatement validated.statement)) fun encoded =>
 RS.bind (RS.ofOption encoded .invalidInstructionData) fun publicBytes =>
 afterPublic L V verify validated proofData checkpointData publicBytes

def afterValidate (L : PoolLib) (V : V2Lib)
 (verify : VerifyArgs → Spec (Except V.VErr Unit)) (a : Args)
 (validated : TX2_242.Validated L) : RS Unit :=
 RS.bind (RS.index a.accounts 0) fun acc0 =>
 RS.bind (RS.ofExcept acc0.data) fun proofData =>
 RS.bind (RS.index a.accounts 6) fun acc6 =>
 RS.bind (RS.ofExcept acc6.data) fun checkpointData =>
 afterReads L V verify validated proofData checkpointData

def replay (L : PoolLib) (V : V2Lib)
 (validate : TX2_242.Args → Env → Obs (Except ProgramError (TX2_242.Validated L)))
 (verify : VerifyNative V) (a : Args) : RS Unit :=
 RS.seq (RS.check (a.accounts.length != 7 || decide (a.data.length < 4)
                  || a.data.take 4 != REQUEST_MAGIC) .invalidInstructionData) <|
 RS.bind (observed validate ⟨a.program_id,a.accounts,a.data,a.current_slot⟩)
   (afterValidate L V (observed verify) a)

def modelVerify (V : V2Lib) : VerifyArgs → Spec (Except V.VErr Unit) :=
 Spec.call (Dom064 V) (fun x => V.tx2auth x.1 x.2.1 x.2.2)

/-- A small definitional factor, keeping numeric guards symbolic. -/
theorem factor (L : PoolLib) (D : DeployedIds) (V : V2Lib) (a : Args) :
 Ref L D V a =
 RS.seq (RS.check (a.accounts.length != 7 || decide (a.data.length < 4)
                  || a.data.take 4 != REQUEST_MAGIC) .invalidInstructionData)
  (RS.bind (Spec.call TX2_242.Domain (TX2_242.Ref L D)
    ⟨a.program_id,a.accounts,a.data,a.current_slot⟩)
   (afterValidate L V (modelVerify V) a)) := rfl

#print axioms factor
end NMS_RSL241Replay
