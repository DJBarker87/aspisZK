import R1Z.PV_RunJoin_EncoderValue49
import R1Z.PV_RunJoin_EncoderOps49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EncoderInstalled49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (amap)
open ProverRwDictionaryTower (fromW)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_EncoderCell49 (S)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (q : Array S 1024#usize) (x y : S) :
    PV_DL_EncoderNative.value
      (@aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField (types base) (selected base heap box ops))
      (amap fromW q) ⟨fromW x,fromW y⟩=
      mapResult fromW (PV_RunJoin_EncoderValue49.run q x y) :=
  PV_RunJoin_EncoderValue49.complete _ fromW
    (PV_RunJoin_EncoderFields49.zero base heap box ops)
    (PV_RunJoin_EncoderFields49.one base heap box ops)
    (PV_RunJoin_EncoderOps49.mul base heap box ops)
    (PV_RunJoin_EncoderOps49.add base heap box ops)
    (PV_RunJoin_EncoderOps49.sub base heap box ops) q x y
#print axioms complete
end R1Z.PV_RunJoin_EncoderInstalled49
