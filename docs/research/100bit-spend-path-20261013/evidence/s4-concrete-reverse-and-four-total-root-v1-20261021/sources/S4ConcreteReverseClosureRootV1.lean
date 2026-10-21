import S4ConcreteReverseHeadRootV1
import S4OldTermBodyReverseV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsConcreteReverseClosureRootV1
open AspisR1FastDotsCurrent
open AspisR1FastDotsConcreteReverseHeadRootV1

theorem old_term_body_success_fixed_body
    (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter : Range) (sums : Array U64 8#usize)
    (flow : ControlFlow (Range × Array U64 8#usize) (Array U64 8#usize))
    (hcount : ops.wideLimbCount = .ok 8#usize)
    (hbody : TermOldBody ops q g slot iter sums = .ok flow) :
    TermNewBody ops q g slot iter sums = .ok flow := by
  cases flow with
  | done out => exact old_term_body_done_fixed_body ops q g slot iter sums out hbody
  | cont state =>
    rcases state with ⟨iter',sums'⟩
    exact AspisR1FastDotsOldTermBodyReverseV1.old_body_success_new_body
      ops q g slot iter iter' sums sums' hcount hbody

theorem old_head_success_fixed_head
    (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter : StepBy) (limbs out : Array U64 8#usize)
    (hcount : ops.wideLimbCount = .ok 8#usize) (hstep : iter.step_by = 4#usize)
    (hloop : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      ops iter q g slot limbs = .ok out) :
    fast_dots.four_dots_one_loop0 ops iter q g slot limbs = .ok out := by
  apply AspisR1FastDotsReverseOuterHeadLoopRootV1.old_head_loop_success_fixed_head_loop
    ops q g slot iter limbs out ?_ hstep hloop
  intro cursor state flow _hstep hold
  apply AspisR1FastDotsReverseBatchBodyRootV1.old_batch_body_success_fixed_body
    ops q g slot cursor state flow hcount ?_ hold
  intro termRange initial result hterms
  exact AspisR1FastDotsReverseTermLoopRootV1.old_term_loop_success_fixed_term_loop
    ops q g slot termRange initial result
    (fun cursor state flow hbody => old_term_body_success_fixed_body
      ops q g slot cursor state flow hcount hbody) hterms

theorem installed_reverse_head (base : Ops) (q : Array U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) :
    AspisR1FastDotsInstalledReverseHelperRootV1.ReverseHeadSuccess
      (install base) q g slot := by
  intro iter limbs out hstep hloop
  exact old_head_success_fixed_head (install base) q g slot iter limbs out rfl hstep hloop

/-- The former ReverseHeadSuccess premise is discharged by the actual inner,
term, fold and StepBy-loop proofs. Canonical-domain hypotheses are explicit;
this is a selected-operation-chain result, not Rust Std/source adoption. -/
theorem fixed_four_total_on_slots
    (base : Ops) (q : Slice U8) (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (hq : 608 ≤ q.length) (ha : a.val = q.val.slice 0 (608#usize))
    (hcoords : ∀ j : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hslots : ∀ slot : Usize, slot.val < 4 →
      AspisR1FastDotsFourCallbacksForwardRootV1.SlotInput a g slot) :
    ∃ values : Array Wide 4#usize,
      fast_dots.four_dots_fixed (install base) q g = .ok values ∧
      (∀ x ∈ values.val, AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) := by
  exact AspisR1FastDotsInstalledReverseHelperRootV1.fixed_four_total_on_slots
    base q a g hq ha hcoords hslots (fun slot _ => installed_reverse_head base a g slot)

#print axioms old_term_body_done_fixed_body
#print axioms old_term_body_success_fixed_body
#print axioms old_head_success_fixed_head
#print axioms installed_reverse_head
#print axioms fixed_four_total_on_slots
end AspisR1FastDotsConcreteReverseClosureRootV1
