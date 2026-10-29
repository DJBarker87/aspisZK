import R1Z.PV_RunJoin_GammaCellTransport50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaRowActual50
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
    (c : Columns) (powers : Array S 29#usize) (row : Usize) (hr : row.val<1024) :
    @prover.opening_row (types base) (selected base heap box ops)
      (Array.to_slice (amap (amap fromW) c)) (amap fromW powers) row=
        mapResult fromW (AspisR1ProducerRelease47.gamma53.cell c powers row 0#usize 29#u8
          AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  rw [PV_RunJoin_BatchRowThread44.caller,PV_RunJoin_InactiveFields48.zero base heap box ops]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_GammaCellTransport50.complete base heap box ops c powers row hr 29 0#usize (by decide)]
  rw [PV_RunJoin_GammaSourceCell50.complete c powers row 29 29#u8 rfl 0#usize (by decide)]
#print axioms complete
end R1Z.PV_RunJoin_GammaRowActual50
