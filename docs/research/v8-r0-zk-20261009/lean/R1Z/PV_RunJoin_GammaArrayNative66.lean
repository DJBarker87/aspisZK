import R1Z.PV_RunJoin_GammaActualInputs50
import R1Z.PV_RunJoin_GammaBatchNative66
import R1Z.PV_RunJoin_NativeResidual63
import R1Z.PV_RunJoin_MappedSuccess50
import R1Z.PV_RunJoin_PrefixImage50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaArrayNative66
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (amap)
open ProverRwDictionaryTower (fromW toW)
open PV_RunJoin_ClaimThread48 (Column W)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (powers : ∀ x, @ExternalFuns.op254 (types base) ops 29#usize x=
      PV_RunJoin_WeightMap46.mapResult (amap fromW) (AspisR1ProducerRelease47.gamma (toW x)))
    (columns : Slice Column) (length : columns.length=29) (g : W) (out : alloc.vec.Vec W)
    (h : @prover.opening_batch (types base)
      (selected base heap box ops)
      columns g=ok out) :
    ∃ a : Array ProverCommitWideOps48.Source 1024#usize,
      ProverCommitGammaOutput53.run (PV_RunJoin_GammaActualInputs50.table columns length) (toW g)=ok a ∧
      out=PV_RunJoin_PrefixFold50.image fromW a ∧ out.length=1024 ∧
      alloc.vec.Vec.deref out=Array.to_slice (amap fromW a) := by
  have frame := PV_RunJoin_GammaBatchNative66.complete base heap box ops powers
    (PV_RunJoin_GammaActualInputs50.table columns length) (toW g)
  rw [PV_RunJoin_GammaActualInputs50.native,ProverRwDictionaryTower.w_roundtrip] at frame
  rw [frame] at h
  obtain ⟨a,ha,he⟩ := PV_RunJoin_MappedSuccess50.complete _ _ _ h
  refine ⟨a,ha,he.symm,?_,?_⟩
  · rw [←he];exact PV_RunJoin_PrefixImage50.length _ _
  · rw [←he];exact PV_RunJoin_PrefixImage50.slice _ _
theorem residual {S F : Type} (base : ExternalTypes)
    (ops : @ExternalFuns (PV_RunJoin_NativeResidual63.types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (PV_RunJoin_NativeResidual63.types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (x : W) :
    @ExternalFuns.op254 (PV_RunJoin_NativeResidual63.types base)
      (PV_RunJoin_NativeResidual63.residual base ops runtime world) 29#usize x=
      PV_RunJoin_WeightMap46.mapResult (amap fromW) (AspisR1ProducerRelease47.gamma (toW x)) := by
  change PV_B1_ActualInstall.powers 29#usize x=_
  exact PV_RunJoin_NativePowerBinding66.gamma x
#print axioms residual
#print axioms complete
end R1Z.PV_RunJoin_GammaArrayNative66
