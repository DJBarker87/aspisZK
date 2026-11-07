import NMX_Semantics
import NMX_HeterogeneousPrimitives
set_option autoImplicit false
namespace LIB_RegistryTransportReuse
open Aeneas Aeneas.Std NMX_OwnedPackets NMX_RawChildren
/-- Typed interface boundary keeps the large registry reference folded. -/
def model (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RegistryArgs) : RSL.RS Unit :=
 @RSL.Spec.call RSL.TX2_234.Args (Except RSL.ProgramError Unit)
  RSL.TX2_234.Domain (RSL.TX2_234.Ref L D)
  (NMX_CallArguments.registry a.verifier a.pool a.masterAccount a.master a.registry a.entry a.slot)

theorem packet (native : RegistryNative) (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (law : RowSpec_234 L D native) (a : RegistryArgs) :
 @NMX_Heterogeneous.Refines Unit Unit id (fun env o => o = native a env) (model L D a) := by
 intro env o run
 subst o
 rw [NMX_HeterogeneousPrimitives.map_identity]
 exact ⟨True.intro,law a env⟩

#print axioms packet
end LIB_RegistryTransportReuse
