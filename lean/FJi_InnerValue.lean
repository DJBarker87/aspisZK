import FJi_InnerStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_InnerValue
open Aeneas Aeneas.Std Result
open FJi_Accumulations FJi_InnerStep
open FJf_U64Array (cell)
/-- SAME selected q/g, natural VALUES for every lane of an accepted inner group.
This has no precomputed result, overflow, decoder, or arithmetic-value premise. -/
theorem value (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (iter : FIo_RangeNext.Range) (seed out : Sums)
    (ordered : iter.start.val ≤ iter.end.val) (small : iter.end.val ≤ 26)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 iter q g slot seed=ok out) :
    Post q g slot iter.start.val iter.end.val seed out := by
  apply FIo_LoopInvariant.preserve
    (fun t : State => FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot t.1 t.2)
    (Inv q g slot iter.start.val iter.end.val seed)
    (Post q g slot iter.start.val iter.end.val seed) measure
    (fun t h r hr => by cases r  <;> exact step q g slot iter.start.val iter.end.val seed t small h _ hr)
    (iter,seed) out ?_ run
  dsimp only [FJi_InnerStep.Inv]
  refine ⟨rfl,by omega,ordered,?_⟩
  intro j hj
  simp only [Nat.sub_self,sum,Nat.add_zero]

/-- Group starts and width are supplied by the source outer iterator. -/
theorem group (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (iter : FIo_RangeNext.Range) (out : Sums)
    (ordered : iter.start.val ≤ iter.end.val) (small : iter.end.val ≤ 26)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 iter q g slot
      (Array.repeat 8#usize 0#u64)=ok out) (j : Nat) (hj : j < 8) :
    (cell out j).val=sum q g slot j iter.start.val (iter.end.val-iter.start.val) := by
  have h := value q g slot iter (Array.repeat 8#usize 0#u64) out ordered small run j hj
  have zero : cell (Array.repeat 8#usize 0#u64) j=0#u64 := by
    unfold cell Array.repeat
    rw [List.getElem?_replicate]
    simp only [show j < (8#usize).val from hj,if_true,Option.getD_some]
  simpa only [zero,show (0#u64).val=0 from rfl,Nat.zero_add] using h
#print axioms value
#print axioms group
end AspisR1.FJi_InnerValue
end
