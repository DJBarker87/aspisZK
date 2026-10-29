import R1Z.PV_RunJoin_GammaRowActual50
import R1Z.PV_RunJoin_PrefixFold50
import R1Z.PV_RunJoin_BatchThread44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaVecTransport50
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
    (c : Columns) (powers : Array S 29#usize) (n : Nat) (out : alloc.vec.Vec W) (row : Usize)
    (bound : row.val+n≤1024) :
    @PV_RunJoin_BatchThread44.phase (types base) (selected base heap box ops)
      (Array.to_slice (amap (amap fromW) c)) (amap fromW powers) n out row=
        PV_RunJoin_PrefixFold50.vecRun (fun j => mapResult fromW
          (AspisR1ProducerRelease47.gamma53.cell c powers j 0#usize 29#u8
            AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO)) n out row := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  induction n generalizing out row with
  | zero => rfl
  | succ n ih =>
    simp only [PV_RunJoin_BatchThread44.phase,PV_RunJoin_BatchThread44.step,PV_RunJoin_PrefixFold50.vecRun,bind_assoc]
    rw [PV_RunJoin_GammaRowActual50.complete base heap box ops c powers row (by omega)]
    apply congrArg (Aeneas.Std.bind _)
    funext value
    apply congrArg (Aeneas.Std.bind _)
    funext next
    exact ih next _ (by rw [PV_RunJoin_MergeLoop35.increment row (by omega)];omega)
#print axioms complete
end R1Z.PV_RunJoin_GammaVecTransport50
