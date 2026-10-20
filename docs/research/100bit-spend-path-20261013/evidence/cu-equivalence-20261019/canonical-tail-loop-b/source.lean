import CuSavingsCanonicalTailStep
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace AspisR1.CuSavingsCanonicalTailLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1CanonicalDots
open CuSavingsCanonicalDotsPush CuSavingsCanonicalDotsField
open CuSavingsCanonicalVectorLoop CuSavingsCanonicalTailStep OccupancyRangeTraversal
variable [Shared] [VectorCommon]

theorem unroll_cont {S V O : Type} (body : S→Result (ControlFlow S V)) (state : S)
    (front : Result S) (hb : body state=(do let next←front;.ok (.cont next)))
    (k : V→Result O) :
    (do let value←loop body state;k value) =
      (do let next←front;let value←loop body next;k value) := by
  rw [loop,hb]
  cases front <;> rfl

theorem old_step {O : Type} (k : old_pairing.EbyKDot→Result O)
    (iter next : Range) (q : Slice U8) (g : G) (slot : Usize) (dot : old_pairing.EbyKDot)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some iter.start,next)) :
    (do let state←old_callers.tail_loop iter q g slot dot;k state) = (do
      let (value,scalar)←input q g slot iter.start
      let after←oldAdvance dot value scalar
      let state←old_callers.tail_loop next q g slot after
      k state) := by
  let front : Result (Range × old_pairing.EbyKDot) := do
    let (value,scalar)←input q g slot iter.start
    let after←oldAdvance dot value scalar
    .ok (next,after)
  have hb : old_callers.tail_loop.body q g slot iter dot=
      (do let state←front;.ok (.cont state)) := by
    simp only [old_callers.tail_loop.body,hn,bind_tc_ok,uncurry_apply_pair,
      front,input,oldAdvance,bind_assoc_eq]
    rfl
  unfold old_callers.tail_loop
  rw [unroll_cont _ _ front hb k]
  simp only [front,bind_assoc_eq,bind_tc_ok,uncurry_apply_pair]

theorem new_step {O : Type} (k : new_pairing.EbyKDot→Result O)
    (iter next : Range) (q : Slice U8) (g : G) (slot : Usize) (dot : new_pairing.EbyKDot)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some iter.start,next)) :
    (do let state←new_callers.tail_loop iter q g slot dot;k state) = (do
      let (value,scalar)←input q g slot iter.start
      let after←newAdvance dot value scalar
      let state←new_callers.tail_loop next q g slot after
      k state) := by
  let front : Result (Range × new_pairing.EbyKDot) := do
    let (value,scalar)←input q g slot iter.start
    let after←newAdvance dot value scalar
    .ok (next,after)
  have hb : new_callers.tail_loop.body q g slot iter dot=
      (do let state←front;.ok (.cont state)) := by
    simp only [new_callers.tail_loop.body,hn,bind_tc_ok,uncurry_apply_pair,
      front,input,newAdvance,bind_assoc_eq]
    rfl
  unfold new_callers.tail_loop
  rw [unroll_cont _ _ front hb k]
  simp only [front,bind_assoc_eq,bind_tc_ok,uncurry_apply_pair]

theorem source_transport {O : Type} (fuel : Nat)
    (newK : new_pairing.EbyKDot→Result O) (oldK : old_pairing.EbyKDot→Result O)
    (hk : ∀ state,RelatedCounts state→newK (project state)=oldK state)
    (iter : Range) (q : Slice U8) (g : G) (hg : CanonicalG g) (slot : Usize)
    (dot : old_pairing.EbyKDot) (hc : RelatedCounts dot)
    (he : iter.end.val=2) (hi : iter.start.val≤2) (hf:2-iter.start.val=fuel) :
    (do let state←new_callers.tail_loop iter q g slot (project dot);newK state) =
      (do let state←old_callers.tail_loop iter q g slot dot;oldK state) := by
  induction fuel generalizing iter dot with
  | zero =>
      have hn := next_done iter (by omega)
      unfold new_callers.tail_loop old_callers.tail_loop
      rw [loop,loop]
      simp only [new_callers.tail_loop.body,old_callers.tail_loop.body,
        hn,bind_tc_ok,uncurry_apply_pair]
      exact hk dot hc
  | succ fuel ih =>
      obtain ⟨next,hn,hinc,hend,_⟩ := next_step iter (by omega)
      rw [new_step newK iter next q g slot (project dot) hn,
        old_step oldK iter next q g slot dot hn]
      apply (bind_eq_iff (input q g slot iter.start) _ _).mpr
      intro pair hp
      rcases pair with ⟨value,scalar⟩
      have hv := input_canonical q g hg slot iter.start value scalar hp
      simp only [uncurry_apply_pair]
      rw [advance_eq dot value scalar hv hc]
      simp only [bind_assoc_eq,bind_tc_ok]
      apply (bind_eq_iff (oldAdvance dot value scalar) _ _).mpr
      intro after ha
      exact ih next after (advance_counts dot after value scalar hv hc ha)
        (by rw [hend];exact he) (by omega) (by omega)

#print axioms unroll_cont
#print axioms old_step
#print axioms new_step
#print axioms source_transport
end AspisR1.CuSavingsCanonicalTailLoop
