import NMX_R2_NativeCanonical
import NMX_R2_NativeBounds
import NMX_R2_ArgsInjection
set_option autoImplicit false
noncomputable section
namespace NMX_R2_RepresentedFold
open Aeneas Aeneas.Std AdapterRw NMX_SourceModel
/-- Reification recovers the SAME complete native input, not just its keys. -/
theorem native_roundtrip (a : NMX_RowSpec_233.Args) :
 NMX_R2_ArgsReify.reify (NMX_R2_CallArguments.auth a) (NMX_R2_NativeBounds.args a) = a := by
 apply NMX_R2_ArgsInjection.injective
 exact NMX_R2_ArgsReify.roundtrip _ _

/-- Canonical Ref transport on represented arguments. Bounds remain explicit
representation facts in this support theorem; canonical Domain stays True. -/
theorem fold (owners : Owners) (alloc : NMX_R2_NativeExecution.Allocations) (failure : Error)
 (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_CanonicalChildren.Registry)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : RSL.TX2_217.RowSpec_217 (NMX_R2_LaneView.view ln))
 (registryPacket : RSL.TX2_234.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (a : RSL.TX2_233.Args) (represented : NMX_R2_ArgsReify.Bounds a) (env : RSL.Env) :
 RSL.TX2_233.Ref (NMX_R2_DecoderLibrary.install L) D a env
  (let native := NMX_R2_ArgsReify.reify a represented
   NMX_R2_NativeExecution.run owners alloc failure ln (NMX_R2_CanonicalChildren.registry rn) env
    (NMX_R2_Skeleton.auth native.program native.accounts native.pool native.lane native.slot)) := by
 let native := NMX_R2_ArgsReify.reify a represented
 have result : RSL.TX2_233.Ref (NMX_R2_DecoderLibrary.install L) D
  (NMX_R2_CallArguments.auth native) env
  (NMX_R2_NativeExecution.run owners alloc failure ln (NMX_R2_CanonicalChildren.registry rn) env
   (NMX_R2_Skeleton.auth native.program native.accounts native.pool native.lane native.slot)) :=
  NMX_R2_NativeCanonical.fold owners alloc failure ln rn L D lanePacket registryPacket
   native.program native.accounts native.pool native.lane native.slot env
 dsimp only [native] at result
 rw [NMX_R2_ArgsReify.roundtrip] at result
 exact result
#print axioms native_roundtrip
#print axioms fold
end NMX_R2_RepresentedFold
end
