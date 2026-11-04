import NFF_LoggedLoop
import NFE_NFA_BatchDomain
import NFE_NFA_OuterStep
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AspisR1.NFF_LoggedOuterStep
open Aeneas Aeneas.Std Result ControlFlow

def step (oracle : NFF_LoggedEight.Oracle) (q : Array U8 608#usize)
    (g : NEV_DotInputs.Coefficients) (slot : Usize)
    (iter : NFA_Iterator.Iter) (limbs : Array U64 8#usize) :
    Result (ControlFlow (NFA_Iterator.Iter × Array U64 8#usize) (Array U64 8#usize)) := do
  let (o,next) ← core.iter.adapters.step_by.IteratorStepBy.next
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done limbs)
  | some start => do
    let stop ← start+4#usize
    let stop ← core.cmp.min core.cmp.OrdUsize stop 26#usize
    let sums ← NFF_LoggedLoop.run oracle q g slot (stop.val-start.val)
      {start,«end»:=stop} (Array.repeat 8#usize 0#u64)
    let out ← NFE_NFA_FoldEight.eight sums limbs
    ok (cont (next,out))

theorem active (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (domain : NEV_DotInputs.Canonical g) (slot : Usize)
    (iter : NFA_Iterator.Iter) (limbs : Array U64 8#usize)
    (stride : iter.step_by.val=4) (finish : iter.iter.end.val=26)
    (inside : iter.iter.start.val < iter.iter.end.val) :
    step oracle q g slot iter limbs=
      FIp_NativeDots.fast_dots.four_dots_one_loop0.body q g slot iter limbs := by
  obtain ⟨cursor,advance,start,endpoint,stride'⟩:=NFA_Iterator.next iter stride inside
  obtain ⟨end4,stop,add,minimum,ordered,stopBound,width,meaning⟩:=
    NFE_NFA_BatchDomain.endpoint iter.iter.start (by omega)
  have inner:=NFF_LoggedLoop.replay oracle law q g domain slot
    (stop.val-iter.iter.start.val) {start:=iter.iter.start,«end»:=stop}
    (Array.repeat 8#usize 0#u64) 0 (by omega) (by dsimp only;omega) stopBound
    NFE_NEV_DotEightTotal.zero
  rw [NFE_NFA_OuterStep.body]
  simp only [step,NFE_NFA_OuterStep.step,advance,add,minimum,bind_tc_ok,Aeneas.Std.uncurry,inner]

theorem stopped (oracle : NFF_LoggedEight.Oracle) (q : Array U8 608#usize)
    (g : NEV_DotInputs.Coefficients) (slot : Usize)
    (iter : NFA_Iterator.Iter) (limbs : Array U64 8#usize)
    (halt : iter.iter.end.val ≤ iter.iter.start.val) :
    step oracle q g slot iter limbs=ok (done limbs) ∧
    FIp_NativeDots.fast_dots.four_dots_one_loop0.body q g slot iter limbs=ok (done limbs) := by
  rw [NFE_NFA_OuterStep.body]
  simp only [step,NFE_NFA_OuterStep.step,NFA_Iterator.stopped iter halt,bind_tc_ok,Aeneas.Std.uncurry]
  trivial

#print axioms active
#print axioms stopped
end AspisR1.NFF_LoggedOuterStep
end
