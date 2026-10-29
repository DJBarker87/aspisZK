import R1Z.PV_RunJoin_GammaOps50
import R1Z.PV_RunJoin_ArrayReadMap50
import R1Z.PV_RunJoin_GammaSourceCell50
import R1Z.PV_RunJoin_BatchRowThread44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaCellStep50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (amap)
open ProverRwDictionaryTower (fromW)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_GammaSourceCell50 (Columns)
abbrev S := ProverCommitWideOps48.Source
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (c : Columns) (powers : Array S 29#usize) (row lane : Usize)
    (hr : row.val<1024) (hl : lane.val<29) (acc : S) :
    @PV_RunJoin_BatchRowThread44.step (types base) (selected base heap box ops)
      (Array.to_slice (amap (amap fromW) c)) (amap fromW powers) row lane (fromW acc)=
        mapResult fromW (PV_RunJoin_GammaSourceCell50.run c powers row lane acc) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  unfold PV_RunJoin_BatchRowThread44.step PV_RunJoin_GammaSourceCell50.run
  rw [PV_RunJoin_ArrayReadMap50.array fromW powers lane hl,
    PV_RunJoin_ArrayReadMap50.slice (amap fromW) c lane hl,
    ProverCommitArrayIndex25.array_index_usize_ok powers lane hl,
    ProverCommitArrayIndex25.array_index_usize_ok c lane hl]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_ArrayReadMap50.array fromW _ row hr,
    ProverCommitArrayIndex25.array_index_usize_ok _ row hr]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_GammaOps50.mul base heap box ops]
  symm
  apply PV_RunJoin_WeightMap46.map_bind fromW fromW
  intro product
  exact (PV_RunJoin_GammaOps50.add base heap box ops acc product).symm
#print axioms complete
end R1Z.PV_RunJoin_GammaCellStep50
