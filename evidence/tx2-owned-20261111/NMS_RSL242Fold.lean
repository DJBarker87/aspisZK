import NMS_RSLRefine
set_option autoImplicit false
namespace NMS_RSL242Fold
open RSL NMS_RSLRefine
/-- The canonical parent control fold with an actual 233 observation at the
original five arguments. All CLOSED child fields keep their complete Specs.
This relation is source support until the emitted-body interpretation is
installed; it does not assert a physical native producer. -/
def replay (L : PoolLib) (D : DeployedIds)
 (authenticate : TX2_233.Args → Env → Obs (Except ProgramError Authenticated))
 (a : TX2_242.Args) : RS (TX2_242.Validated L) :=
  RS.seq (RS.check (a.instruction_data.length != REQUEST_BYTES) .invalidInstructionData) <|
  RS.bind (RS.ofOption (L.decodeRequest a.instruction_data) .invalidInstructionData) fun q =>
  RS.seq (RS.check (decide (L.reqProfile q ≠ PROFILE_BINDING)
                    || decide (L.reqRelease q ≠ RELEASE_BINDING)
                    || decide (L.reqPoolProgram q ≠ D.pool)) .invalidInstructionData) <|
  let pool := L.reqPoolProgram q
  RS.bind (RS.ofOption (L.outputLane (L.reqNullifier q)) .invalidInstructionData) fun lane =>
  RS.bind (RS.ofExcept a.current_slot) fun slot =>
  RS.bind (observed authenticate ⟨a.verifier_program,a.accounts,pool,lane,slot⟩) fun auth =>
  RS.bind (RS.ofOption a.accounts.head? .notEnoughAccountKeys) fun proofAccount =>
  RS.bind (RS.ofExcept proofAccount.data) fun pdata =>
  RS.bind (L.scanProof pdata) fun scanned =>
  RS.bind (L.reconstruct q auth scanned.1) fun statement =>
  RS.pure { statement := statement, proof_length := scanned.2 }

/-- The full 233 packet is sufficient, including errors and stopped prefixes;
no returned reply, successful child, Root0 or post-abort state is assumed. -/
theorem fold (L : PoolLib) (D : DeployedIds)
 (authenticate : TX2_233.Args → Env → Obs (Except ProgramError Authenticated))
 (packet : TX2_233.RowSpec_233 L D authenticate) (a : TX2_242.Args) :
 Refines (replay L D authenticate a) (TX2_242.Ref L D a) := by
 unfold replay TX2_242.Ref
 apply rsseq (refl _)
 apply rsbind (refl _)
 intro q
 apply rsseq (refl _)
 apply rsbind (refl _)
 intro lane
 apply rsbind (refl _)
 intro slot
 apply rsbind (call TX2_233.Domain (TX2_233.Ref L D) authenticate packet _ trivial)
 intro auth
 exact refl _

#print axioms fold
end NMS_RSL242Fold
