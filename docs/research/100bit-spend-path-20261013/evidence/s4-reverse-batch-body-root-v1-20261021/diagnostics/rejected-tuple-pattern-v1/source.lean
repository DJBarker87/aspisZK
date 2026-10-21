import S4OldLimbLoopFoldEightV1
import S4ReverseTermLoopRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsReverseBatchBodyRootV1
open AspisR1FastDotsNewOuterLimbLoopSegmentV1 (foldEight)
open AspisR1FastDotsCurrent
abbrev Ops := FourDotsOps
abbrev Wide := aspis_core.field.wide_exact.WideExact
abbrev StepBy := AspisR1FastDotsBatchBodyAdvance.StepBy
abbrev NewBody := fast_dots.four_dots_one_loop0.body
abbrev OldBody := fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
abbrev OldTermLoop := AspisR1FastDotsNewTermLoopOldLoopTransferV1.OldLoop
abbrev NewTermLoop := AspisR1FastDotsNewTermLoopOldLoopTransferV1.NewLoop

private theorem result_bind_assoc {A B C : Type} (r : Result A)
    (f : A → Result B) (k : B → Result C) :
    ((r >>= f) >>= k) = (r >>= fun x => f x >>= k) := by cases r <;> rfl

private theorem bind_ok_inv {A B : Type} {r : Result A} {f : A → Result B} {x : B}
    (h : (r >>= f) = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

def groupedFixedBody (ops : Ops) (q : Array U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (iter : StepBy)
    (limbs : Array U64 8#usize) := do
  let (o,it) ← core.iter.adapters.step_by.IteratorStepBy.next
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (ControlFlow.done limbs)
  | some start => do
    let stop ← start + 4#usize
    let stop1 ← core.cmp.min core.cmp.OrdUsize stop 26#usize
    let sums ← NewTermLoop ops {start, «end» := stop1} q g slot (Array.repeat 8#usize 0#u64)
    let updated ← foldEight sums limbs
    ok (ControlFlow.cont (it,updated))

theorem fixed_body_eq_grouped (ops : Ops) (q : Array U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (iter : StepBy) (limbs : Array U64 8#usize) :
    NewBody ops q g slot iter limbs = groupedFixedBody ops q g slot iter limbs := by
  unfold NewBody fast_dots.four_dots_one_loop0.body groupedFixedBody foldEight
  simp only [result_bind_assoc,bind_tc_ok]

/-- Complete batch-body reverse transfer. The eight-limb fold reverse law is
proved, not assumed here; only the separate term-loop reverse law remains. -/
theorem old_batch_body_success_fixed_body
    (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter : StepBy) (limbs : Array U64 8#usize)
    (flow : ControlFlow (StepBy × Array U64 8#usize) (Array U64 8#usize))
    (hcount : ops.wideLimbCount = .ok 8#usize)
    (hterms : ∀ (r : core.ops.range.Range Usize) (initial out : Array U64 8#usize),
      OldTermLoop ops r q g slot initial = .ok out →
      NewTermLoop ops r q g slot initial = .ok out)
    (hold : OldBody ops q g slot iter limbs = .ok flow) :
    NewBody ops q g slot iter limbs = .ok flow := by
  unfold OldBody fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body at hold
  obtain ⟨⟨o,it⟩,hnext,hrest⟩ := bind_ok_inv hold
  rw [fixed_body_eq_grouped]
  unfold groupedFixedBody
  rw [hnext,bind_tc_ok]
  cases o with
  | none => exact hrest
  | some start =>
    obtain ⟨stop,hadd,hrest⟩ := bind_ok_inv hrest
    obtain ⟨stop1,hmin,hrest⟩ := bind_ok_inv hrest
    obtain ⟨sums,hOldTerms,hrest⟩ := bind_ok_inv hrest
    rw [hcount,bind_tc_ok] at hrest
    obtain ⟨updated,hOldFold,hfinal⟩ := bind_ok_inv hrest
    have hNewTerms := hterms {start, «end» := stop1} (Array.repeat 8#usize 0#u64) sums hOldTerms
    have hNewFold := AspisR1FastDotsOldLimbLoopFoldEightV1.old_limb_loop_success_foldEight
      ops sums limbs updated hOldFold
    simp only [hadd,bind_tc_ok,hmin,hNewTerms,hNewFold]
    exact hfinal

#print axioms fixed_body_eq_grouped
#print axioms old_batch_body_success_fixed_body
end AspisR1FastDotsReverseBatchBodyRootV1
