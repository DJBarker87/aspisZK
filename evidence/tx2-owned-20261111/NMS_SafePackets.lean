import NMS_CloneReference
import RSL_TX2_241
set_option autoImplicit false
namespace NMS_SafePackets
open RSL NMS_CloneReference
/-- Proposed OWN-INPUT clause needed for CLOSED NHJ_DataPacket.substitute's
recorded clone domain. The actual snapshot caller establishes it (see
NMS_SnapshotErrors.snapshot). It is recorded as a difference from RSL's True
242 domain; no canonical-domain equivalence is asserted. -/
def LengthErrors (a : OwnedAccount) : Prop :=
 ∀ error, a.length = .error error → error = .accountBorrowFailed ∨ error = .invalidAccountData

def Safe (accounts : List OwnedAccount) : Prop :=
 ∀ a ∈ accounts, SnapshotErrors a ∧ LengthErrors a

def RowSpec233 (L : PoolLib) (D : DeployedIds)
 (impl : TX2_233.Args → Env → Obs (Except ProgramError Authenticated)) : Prop :=
 ∀ a env, Safe a.accounts → TX2_233.Ref L D a env (impl a env)

def RowSpec242 (L : PoolLib) (D : DeployedIds)
 (impl : TX2_242.Args → Env → Obs (Except ProgramError (TX2_242.Validated L))) : Prop :=
 ∀ a env, Safe a.accounts → TX2_242.Ref L D a env (impl a env)

def Domain241 (V : TX2_241.V2Lib) (a : TX2_241.Args) : Prop :=
 TX2_241.Domain V a ∧ Safe a.accounts

def RowSpec241 (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (impl : TX2_241.Args → Env → Obs (Except ProgramError Unit)) : Prop :=
 ∀ a env, Domain241 V a → TX2_241.Ref L D V a env (impl a env)

theorem canonical233 (L : PoolLib) (D : DeployedIds)
 (impl : TX2_233.Args → Env → Obs (Except ProgramError Authenticated))
 (packet : TX2_233.RowSpec_233 L D impl) : RowSpec233 L D impl :=
 fun a env _ => packet a env trivial

theorem canonical242 (L : PoolLib) (D : DeployedIds)
 (impl : TX2_242.Args → Env → Obs (Except ProgramError (TX2_242.Validated L)))
 (packet : TX2_242.RowSpec_242 L D impl) : RowSpec242 L D impl :=
 fun a env _ => packet a env trivial

#print axioms canonical233
#print axioms canonical242
end NMS_SafePackets
