import NMX_R3_RegistryNativeFold
import NMX_R3_RegistryProjectionRef
import NMX_R3_RegistryInput
import NMX_R3_RegistryInert
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryRoot
open Aeneas Aeneas.Std AdapterRw

/-- The source interpreter runs at the full canonical input. The projection
only gives a typed representative of its observational class, proved equal
for the full reference relation, including the unrepresentable rejection arm. -/
def authenticate (allocations : RSL.TX2_234.Args → RSL.Env → Nat → Bool)
 (a : RSL.TX2_234.Args) (env : RSL.Env) : RSL.Obs (Except RSL.ProgramError Unit) :=
 let x := NMX_R3_RegistryInput.reify a
 NMX_R3_RegistryNativeFold.execution NMX_R3_RegistryInert.inert LIBB_PoolLib.deployed env (allocations a env)
  x.verifier x.pool x.masterAccount x.master x.registry x.entry x.slot

theorem root (allocations : RSL.TX2_234.Args → RSL.Env → Nat → Bool) :
 RSL.TX2_234.RowSpec_234 LIBB_PoolLib.library LIBB_PoolLib.deployed (authenticate allocations) := by
 intro a env _
 let x := NMX_R3_RegistryInput.reify a
 have h := NMX_R3_RegistryNativeFold.native NMX_R3_RegistryInert.inert LIBB_PoolLib.deployed env
  (allocations a env) x.verifier x.pool x.masterAccount x.master x.registry x.entry x.slot
 change RSL.TX2_234.Ref LIBB_PoolLib.library LIBB_PoolLib.deployed (NMX_R3_RegistryInput.image x) env _ at h
 dsimp only [x] at h
 rw [NMX_R3_RegistryInput.roundtrip,NMX_R3_RegistryProjectionRef.reference] at h
 exact h
#print axioms root
end NMX_R3_RegistryRoot
end
