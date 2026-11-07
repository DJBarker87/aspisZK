import NMX_R2_CanonicalTarget
import NMX_R2_CallArguments
set_option autoImplicit false
namespace NMX_R2_RawChildren
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_R2_Carrier
/-- Full observations on the actual emitted typed argument/result carriers.
These are recorded representation variants of canonical217/234, not their
unproved equality, and not candidate child roots. -/
abbrev LaneNative := Slice U8 → RSL.Env → RSL.Obs (Except RSL.ProgramError (Box Lane))
structure RegistryArgs where
 verifier : solana_pubkey.Pubkey
 pool : solana_pubkey.Pubkey
 masterAccount : r1_pool_adapter.owned.OwnedAccount
 master : Master
 registry : r1_pool_adapter.owned.OwnedAccount
 entry : r1_pool_adapter.owned.OwnedAccount
 slot : U64
abbrev RegistryNative := RegistryArgs → RSL.Env → RSL.Obs (Except RSL.ProgramError Unit)

def mapObs {A B : Type} (f : A → B) (o : RSL.Obs (Except RSL.ProgramError A)) :
 RSL.Obs (Except RSL.ProgramError B) :=
 ⟨match o.exit with
 | .ret (.ok a) => .ret (.ok (f a))
 | .ret (.error e) => .ret (.error e)
 | .abort => .abort
 | .diverge => .diverge,o.events⟩

def RowSpec_217 (native : LaneNative) : Prop :=
 ∀ b env, RSL.TX2_217.Ref (bytes b) env (mapObs (fun box => lane box.payload) (native b env))

def RowSpec_234 (L : RSL.PoolLib) (D : RSL.DeployedIds) (native : RegistryNative) : Prop :=
 ∀ a env, RSL.TX2_234.Ref L D
  (NMX_R2_CallArguments.registry a.verifier a.pool a.masterAccount a.master a.registry a.entry a.slot)
  env (native a env)

theorem lane_prefix (native : LaneNative) (b : Slice U8) (env : RSL.Env) :
 (mapObs (fun box => lane box.payload) (native b env)).events = (native b env).events := rfl
#print axioms lane_prefix
end NMX_R2_RawChildren
