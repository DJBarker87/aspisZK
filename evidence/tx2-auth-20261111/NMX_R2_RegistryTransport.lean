import NMX_R2_Semantics
import NMX_R2_HeterogeneousPrimitives
set_option autoImplicit false
namespace NMX_R2_RegistryTransport
open Aeneas Aeneas.Std NMX_OwnedPackets NMX_R2_RawChildren
/-- Typed interface boundary keeps the large registry reference folded. -/
def model (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RegistryArgs) : RSL.RS Unit :=
 @RSL.Spec.call RSL.TX2_234.Args (Except RSL.ProgramError Unit)
  RSL.TX2_234.Domain (RSL.TX2_234.Ref L D)
  (NMX_R2_CallArguments.registry a.verifier a.pool a.masterAccount a.master a.registry a.entry a.slot)

theorem packet (native : RegistryNative) (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (law : RowSpec_234 L D native) (a : RegistryArgs) :
 @NMX_R2_Heterogeneous.Refines Unit Unit id (fun env o => o = native a env) (model L D a) := by
 intro env o run
 subst o
 rw [NMX_R2_HeterogeneousPrimitives.map_identity]
 exact ⟨True.intro,law a env⟩

#print axioms packet
end NMX_R2_RegistryTransport
