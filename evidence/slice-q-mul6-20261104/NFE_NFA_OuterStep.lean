import NFE_NFA_FoldEight
import NFE_NFA_InnerLoop
import NFA_Iterator
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFE_NFA_OuterStep
open Aeneas Aeneas.Std Result ControlFlow
abbrev Iter := NFA_Iterator.Iter

def step (q : Array U8 608#usize) (g : Array NEV_DotCarrier.NE 29#usize) (slot : Usize)
    (iter : Iter) (limbs : Array U64 8#usize) : Result (ControlFlow (Iter × Array U64 8#usize) (Array U64 8#usize)) := do
  let (o,next) ← core.iter.adapters.step_by.IteratorStepBy.next
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done limbs)
  | some start => do
    let stop ← start+4#usize
    let stop ← core.cmp.min core.cmp.OrdUsize stop 26#usize
    let sums ← FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 {start,«end»:=stop}
      q g slot (Array.repeat 8#usize 0#u64)
    let out ← NFE_NFA_FoldEight.eight sums limbs
    ok (cont (next,out))

theorem body (q : Array U8 608#usize) (g : Array NEV_DotCarrier.NE 29#usize) (slot : Usize)
    (iter : Iter) (limbs : Array U64 8#usize) :
    FIp_NativeDots.fast_dots.four_dots_one_loop0.body q g slot iter limbs=step q g slot iter limbs := by
  simp only [FIp_NativeDots.fast_dots.four_dots_one_loop0.body,step,
    NFE_NFA_FoldEight.eight,NFE_NFA_FoldLane.lane,bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨o,next⟩ run
  cases o <;> simp only [Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok]

#print axioms body
end AspisR1.NFE_NFA_OuterStep
end
