import FJi_OuterStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_OuterValue
open Aeneas Aeneas.Std Result
open FJi_Accumulations FJi_OuterStep
open FJf_U64Array (cell)
/-- Exact seven-group VALUES for all eight lanes on arbitrary SAME q/g.
No whole loop is normalized; the proof uses the checked source iterator. -/
theorem value (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) (out : Sums)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0 (JFs_TX2_Iterator.value 0)
      q g slot (Array.repeat 8#usize 0#u64)=ok out) : Post q g slot out := by
  apply FIo_LoopInvariant.preserve
    (fun s : State => FIp_NativeDots.fast_dots.four_dots_one_loop0.body q g slot s.1 s.2)
    (Inv q g slot) (Post q g slot) measure
    (fun s h r hr => by cases r  <;> exact step q g slot s h _ hr)
    (JFs_TX2_Iterator.value 0,Array.repeat 8#usize 0#u64) out ?_ run
  refine ⟨0,by omega,rfl,rfl,rfl,?_,?_⟩
  · intro x hx
    have same : x=0#u64 := (List.mem_replicate.mp hx).2
    subst x
    simp
  · intro j
    change (cell (Array.repeat 8#usize 0#u64) j.val).val=0
    unfold cell Array.repeat
    rw [List.getElem?_replicate]
    simp only [show j.val < (8#usize).val from j.isLt,if_true,Option.getD_some]
    rfl
#print axioms value
end AspisR1.FJi_OuterValue
end
