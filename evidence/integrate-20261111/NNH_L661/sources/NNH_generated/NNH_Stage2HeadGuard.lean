import NNH_CorrectConfiguration
import NNH_RequestMagic
set_option autoImplicit false
noncomputable section
namespace NNH_Stage2HeadGuard
open Aeneas Aeneas.Std AspisR1 AdapterRw

theorem full (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :
 core.array.Array.index (core.ops.index.IndexSlice
  ((core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice (NNH_CorrectConfiguration.sdk missing env err reserve)) U8))
  NNH_RequestMagic.magic ()=.ok NNH_RequestMagic.magic.to_slice := rfl

theorem equal (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :
 core.cmp.PartialEq.ne.trait_default
  ((core.option.Option.Insts.CoreCmpPartialEqOption (NNH_CorrectConfiguration.sdk missing env err reserve))
   (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8)))
  (some NNH_RequestMagic.magic.to_slice) (some NNH_RequestMagic.magic.to_slice)=.ok false := by
 unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
 change (do
  let b ← core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 NNH_RequestMagic.magic.to_slice NNH_RequestMagic.magic.to_slice
  Result.ok (decide (¬b=true)))=Result.ok false
 rw [NNH_SliceEq.self]
 rfl
#print axioms full
#print axioms equal
end NNH_Stage2HeadGuard
