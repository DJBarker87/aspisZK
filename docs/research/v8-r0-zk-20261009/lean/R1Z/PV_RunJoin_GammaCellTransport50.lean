import R1Z.PV_RunJoin_GammaCellStep50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaCellTransport50
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
    (c : Columns) (powers : Array S 29#usize) (row : Usize) (hr : row.val<1024)
    (n : Nat) (lane : Usize) (bound : lane.val+n≤29) (acc : S) :
    @PV_RunJoin_BatchRowThread44.phase (types base) (selected base heap box ops)
      (Array.to_slice (amap (amap fromW) c)) (amap fromW powers) row n lane (fromW acc)=
        mapResult fromW (PV_RunJoin_GammaSourceCell50.phase c powers row n lane acc) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  induction n generalizing lane acc with
  | zero => rfl
  | succ n ih =>
    rw [PV_RunJoin_BatchRowThread44.phase,PV_RunJoin_GammaSourceCell50.phase,
      PV_RunJoin_GammaCellStep50.complete base heap box ops c powers row lane hr (by omega)]
    symm
    apply PV_RunJoin_WeightMap46.map_bind fromW fromW
    intro next
    exact (ih (Usize.wrapping_add lane 1#usize)
      (by rw [PV_RunJoin_MergeLoop35.increment lane (by omega)];omega) next).symm
#print axioms complete
end R1Z.PV_RunJoin_GammaCellTransport50
