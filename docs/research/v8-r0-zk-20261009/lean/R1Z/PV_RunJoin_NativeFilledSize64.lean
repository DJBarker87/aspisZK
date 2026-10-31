import R1Z.PV_RunJoin_VectorSize64
import R1Z.PV_RunJoin_NativeFrames63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeFilledSize64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63 PV_RunJoin_ResultPost41

theorem candidate [ExternalTypes] {T : Type} (ops : ExternalFuns) :
    ∃ inner : ExternalFuns, (ProverRwP6BodyCandidate.selected ops).op81 (T:=T)=
      @ProverRwSuccessHeapSource.aspis_core.r0.heap.filled _ inner T := by
  exact ⟨_,rfl⟩

attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected

theorem frame {S F T : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    ∃ inner : @ExternalFuns (types base),
      @ExternalFuns.op81 (types base) (opsNative base heap box ops runtime world) T=
        @ProverRwSuccessHeapSource.aspis_core.r0.heap.filled (types base) inner T := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_81]
  exact @candidate (types base) T (residual base ops runtime world)

theorem complete {S F T : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (copy : core.marker.Copy T) (n : Usize) (value : T) :
    Post (fun status => match status with | .Err _ => True | .Ok v => v.length=n.val)
      (@aspis_core.r0.heap.filled (types base) (opsNative base heap box ops runtime world) T copy n value) := by
  obtain ⟨inner,hi⟩ := frame (T:=T) base heap box ops runtime world
  change Post _ ((opsNative base heap box ops runtime world).op81 copy n value)
  rw [hi]
  exact @PV_RunJoin_VectorSize64.filled (types base) inner T copy n value

#print axioms candidate
#print axioms frame
#print axioms complete
end R1Z.PV_RunJoin_NativeFilledSize64
