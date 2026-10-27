import RPu_FJe_Sum3ChannelStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_Sum3ChannelEdges
open Aeneas Aeneas.Std Result
open FJe_Sum3BridgeBase
def next := core.iter.range.IteratorRange.next core.iter.range.StepUsize
theorem native_done (iter : Range) (a : Left) (s : Sums) (i : Usize) (r : Components) (c : Usize)
    (hn : next iter=ok (none,iter)) :
    FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0 iter a s i r c=ok s := by
  rw [FJe_Sum3ChannelStep.native]
  change (do let z ← next iter;match z.1 with
    | none=>ok s
    | some ch=>
      FJe_Sum3ChannelStep.step a s i r c ch (fun v=>FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0 z.2 a v i r c))=ok s
  rw [hn]
  rfl
theorem old_done (iter : Range) (a : Left) (s : Sums) (i : Usize) (r : Components) (c : Usize)
    (hn : next iter=ok (none,iter)) :
    AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0 iter (left a) s i r c=ok s := by
  rw [FJe_Sum3ChannelStep.old]
  change (do let z ← next iter;match z.1 with
    | none=>ok s
    | some ch=>
      FJe_Sum3ChannelStep.step a s i r c ch (fun v=>AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0 z.2 (left a) v i r c))=ok s
  rw [hn]
  rfl
theorem native_step (iter iter1 : Range) (a : Left) (s : Sums) (i : Usize) (r : Components) (c ch : Usize)
    (hn : next iter=ok (some ch,iter1)) :
    FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0 iter a s i r c=
      FJe_Sum3ChannelStep.step a s i r c ch
        (fun v=>FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0 iter1 a v i r c) := by
  rw [FJe_Sum3ChannelStep.native]
  change (do let z ← next iter;match z.1 with
    | none=>ok s
    | some ch=>
      FJe_Sum3ChannelStep.step a s i r c ch (fun v=>FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0 z.2 a v i r c))=_
  rw [hn]
  rfl
theorem old_step (iter iter1 : Range) (a : Left) (s : Sums) (i : Usize) (r : Components) (c ch : Usize)
    (hn : next iter=ok (some ch,iter1)) :
    AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0 iter (left a) s i r c=
      FJe_Sum3ChannelStep.step a s i r c ch
        (fun v=>AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0 iter1 (left a) v i r c) := by
  rw [FJe_Sum3ChannelStep.old]
  change (do let z ← next iter;match z.1 with
    | none=>ok s
    | some ch=>
      FJe_Sum3ChannelStep.step a s i r c ch (fun v=>AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0 z.2 (left a) v i r c))=_
  rw [hn]
  rfl
#print axioms native_done
#print axioms old_done
#print axioms native_step
#print axioms old_step
end AspisR1.FJe_Sum3ChannelEdges
end
