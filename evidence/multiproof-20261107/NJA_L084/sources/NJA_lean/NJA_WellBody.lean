import NJA_WellPredicates
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace NJA_WellBody
open NJA_Multiproof
impl_def winInst (W : Type) (step : W → Result ((Option (Slice U32)) × W)) :
 core.iter.traits.iterator.Iterator W (Slice U32) := {
 next := step
 enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default (winInst W step)
}
def emitted (W : Type)
 (next : W → Result ((Option (Slice U32)) × W))
 (windows : Slice U32 → Usize → Result W) (indices : Slice Std.U32) : Result Bool := do
  let b ← core.slice.Slice.is_empty indices
  if b
  then ok false
  else
    let i := Slice.len indices
    if i <= multiproof.MAX_BATCH
    then
      let w ← windows indices 2#usize
      let (b1, _) ←
        core.iter.traits.iterator.Iterator.all.default
          (winInst W next)
          multiproof.well_formed.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool
          w ()
      if b1
      then
        let i1 ← core.slice.Slice.iter indices
        let (b2, _) ←
          core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
            multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool
            i1 ()
        ok b2
      else ok false
    else ok false
end NJA_WellBody
end
