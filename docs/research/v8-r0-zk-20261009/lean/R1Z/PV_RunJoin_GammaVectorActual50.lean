import R1Z.PV_RunJoin_GammaSourceFill50
import R1Z.PV_RunJoin_GammaVecTransport50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaVectorActual50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (amap)
open ProverRwDictionaryTower (fromW)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_GammaSourceCell50 (Columns)
abbrev S := ProverCommitWideOps48.Source
abbrev W := aspis_core.field.wide_exact.WideExact
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (c : Columns) (powers : Array S 29#usize) :
    @prover.opening_batch_loop (types base) (selected base heap box ops)
      (Array.to_slice (amap (amap fromW) c)) (amap fromW powers)
      (alloc.vec.Vec.with_capacity W 1024#usize) 0#usize=
        mapResult (PV_RunJoin_PrefixFold50.image fromW) (AspisR1ProducerRelease47.gamma53.all c powers) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  rw [PV_RunJoin_BatchThread44.complete _ _ _ 0#usize 1024 (by rfl),
    PV_RunJoin_GammaVecTransport50.complete base heap box ops c powers 1024 _ 0#usize (by decide)]
  rw [AspisR1ProducerRelease47.gamma53.all,
    PV_RunJoin_GammaSourceFill50.complete c powers 1024 1024#u16 rfl _ 0#usize (by decide)]
  exact PV_RunJoin_PrefixFold50.complete fromW _ 1024 _ _ 0#usize rfl rfl
#print axioms complete
end R1Z.PV_RunJoin_GammaVectorActual50
