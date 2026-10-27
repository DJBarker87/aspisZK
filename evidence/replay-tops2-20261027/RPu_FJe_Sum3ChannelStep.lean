import RPu_FJe_Sum3BridgeBase
import RPu_FJb_PairProjection
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_Sum3ChannelStep
open Aeneas Aeneas.Std Result
open FJe_Sum3BridgeBase
open FIv_NativeArithmetic (bind_map)
open FIv_PreparedNew (prepared)
def step (a : Left) (s : Sums) (i : Usize) (r : Components) (c ch : Usize)
    (k : Sums → Result Sums) : Result Sums := do
  let p ← Array.index_usize a i
  let row ← Array.index_usize p.components c
  let x ← Array.index_usize row ch
  let x64 ← lift (UScalar.cast .U64 x)
  let rr ← Array.index_usize r c
  let y ← Array.index_usize rr ch
  let y64 ← lift (UScalar.cast .U64 y)
  let prod ← x64*y64
  let sr ← Array.index_usize s c
  let old ← Array.index_usize sr ch
  let new ← old+prod
  let (row,back) ← Array.index_mut_usize s c
  let next ← Array.update row ch new
  k (back next)
/-- One exact native loop unfolding,with tuple reduction kept local. -/
theorem native (iter : Range) (a : Left) (s : Sums) (i : Usize) (r : Components) (c : Usize) :
    FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0 iter a s i r c=
      (do
        let z ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
        match z.1 with
        | none => ok s
        | some ch =>
            step a s i r c ch (fun next=>FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0 z.2 a next i r c)) := by
  rw [FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0.eq_def]
  rfl
/-- The old loop uses the identical single integer update after nominal
prepared transport;all checked arithmetic and array operations are retained. -/
theorem old (iter : Range) (a : Left) (s : Sums) (i : Usize) (r : Components) (c : Usize) :
    AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0 iter (left a) s i r c=
      (do
        let z ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
        match z.1 with
        | none => ok s
        | some ch =>
            step a s i r c ch (fun next=>AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0 z.2 (left a) next i r c)) := by
  rw [AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0.eq_def]
  simp only [step,left,FJb_ArrayTransport.index,bind_map,prepared]
  rfl
#print axioms native
#print axioms old
end AspisR1.FJe_Sum3ChannelStep
end
