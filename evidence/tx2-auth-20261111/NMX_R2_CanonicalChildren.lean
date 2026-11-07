import NMX_R2_RawChildren
set_option autoImplicit false
namespace NMX_R2_CanonicalChildren
open RSL
abbrev Registry := TX2_234.Args → Env → Obs (Except ProgramError Unit)
/-- Input-only representation map; the complete Unit/error/stopped observation
is forwarded unchanged. No child reply or argument equality is assumed. -/
def registry (native : Registry) : NMX_R2_RawChildren.RegistryNative := fun a env =>
 native (NMX_R2_CallArguments.registry a.verifier a.pool a.masterAccount a.master a.registry a.entry a.slot) env

theorem registry_packet (L : PoolLib) (D : DeployedIds) (native : Registry)
 (packet : TX2_234.RowSpec_234 L D native) :
 NMX_R2_RawChildren.RowSpec_234 L D (registry native) := by
 intro a env
 exact packet _ env trivial
#print axioms registry_packet
end NMX_R2_CanonicalChildren
