import NNH_SliceEqValue
import NNH_ByteListInjective
import NNH_CorrectConfiguration
set_option autoImplicit false
noncomputable section
namespace NNH_Tx1RouteCompare
open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier
attribute [local instance] Classical.propDecidable

theorem source (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (data : Slice U8) (tag : U8) :
 (NNH_CorrectConfiguration.sdk missing env err reserve).op1 core.cmp.PartialEqU8 data
  (Array.make 2#usize [3#u8,tag])=.ok (decide (bytes data=[3,byte tag])) := by
 change core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 data (Array.make 2#usize [3#u8,tag]).to_slice=_
 rw [NNH_SliceEqValue.value]
 have same : (data.val=[3#u8,tag]) ↔ (bytes data=[3,byte tag]) := by
  constructor
  · intro eq
    unfold bytes
    rw [eq]
    with_unfolding_all rfl
  · intro eq
    apply NNH_ByteListInjective.value
    have small : [3#u8,tag].map byte=[3,byte tag] := by with_unfolding_all rfl
    rw [small]
    exact eq
 change Result.ok (decide (data.val=[3#u8,tag]))=_
 rw [propext same]
#print axioms source
end NNH_Tx1RouteCompare
