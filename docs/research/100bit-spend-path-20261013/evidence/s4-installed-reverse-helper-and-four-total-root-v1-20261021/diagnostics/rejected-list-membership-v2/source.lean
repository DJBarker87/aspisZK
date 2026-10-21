import S4ReverseWholeHelperRootV1
import S4FunctionForwardRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsInstalledReverseHelperRootV1
open AspisR1FastDotsCurrent
open AspisR1FastDotsWholeHelperTransferRootV1 (Ops Wide StepBy)
open AspisR1FastDotsFourCallbacksForwardRootV1 (install SlotInput arrayOps)

/-- This is the exact outstanding head-loop property, not an arbitrary
replacement implementation or an assumed complete helper equality. -/
def ReverseHeadSuccess (ops : Ops) (q : Array U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) : Prop :=
  ∀ (iter : StepBy) (limbs result : Array U64 8#usize),
    iter.step_by = 4#usize →
    fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      ops iter q g slot limbs = .ok result →
    fast_dots.four_dots_one_loop0 ops iter q g slot limbs = .ok result

theorem installed_old_callback_success_fixed_helper
    (base : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (out : Wide)
    (hreverse : ReverseHeadSuccess (install base) q g slot)
    (hold : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      (install base) (q,g) slot = .ok (out,(q,g))) :
    fast_dots.four_dots_one (install base) q g slot = .ok out := by
  exact AspisR1FastDotsReverseWholeHelperRootV1.old_callback_success_fixed_helper
    (install base) q g slot out rfl (fun _ => rfl) hreverse hold

/-- Canonical coefficient coordinates and scanner-derived slot witnesses
supply the successful original callback internally. ReverseHeadSuccess is
still an explicit outstanding dependency; this is not a frozen-source claim. -/
theorem fixed_helper_total_on_slot
    (base : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize)
    (hcoords : ∀ j : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hslot : SlotInput q g slot)
    (hreverse : ReverseHeadSuccess (install base) q g slot) :
    ∃ out : Wide, fast_dots.four_dots_one (install base) q g slot = .ok out ∧
      AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE out) := by
  obtain ⟨hparsed,first,r0,r1,qfirst,q0,q1,hpf,hp0,hp1⟩ := hslot
  obtain ⟨out,hold,hcan⟩ :=
    AspisR1FastDotsFullCallbackForwardRootV1.full_callback_forward
      (arrayOps base) q g slot hcoords hparsed first r0 r1 qfirst q0 q1 hpf hp0 hp1
  exact ⟨out, installed_old_callback_success_fixed_helper
    base q g slot out hreverse hold, hcan⟩


/-- The complete four-call candidate succeeds on the same canonical domain,
conditional only on the still-open reverse head-loop law. Prefix operations
and all four helper successes are derived here, rather than assumed. -/
theorem fixed_four_total_on_slots
    (base : Ops) (q : Slice U8) (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (hq : 608 ≤ q.length) (ha : a.val = q.val.slice 0 (608#usize))
    (hcoords : ∀ j : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hslots : ∀ slot : Usize, slot.val < 4 → SlotInput a g slot)
    (hreverse : ∀ slot : Usize, slot.val < 4 →
      ReverseHeadSuccess (install base) a g slot) :
    ∃ values : Array Wide 4#usize,
      fast_dots.four_dots_fixed (install base) q g = .ok values ∧
      (∀ x ∈ values.val, AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) := by
  obtain ⟨s,hs,hcopy⟩ := AspisR1FastDotsFunctionForwardRootV1.prefix608_forward q a hq ha
  obtain ⟨v0,h0,hc0⟩ := fixed_helper_total_on_slot base a g 0#usize hcoords
    (hslots 0#usize (by decide)) (hreverse 0#usize (by decide))
  obtain ⟨v1,h1,hc1⟩ := fixed_helper_total_on_slot base a g 1#usize hcoords
    (hslots 1#usize (by decide)) (hreverse 1#usize (by decide))
  obtain ⟨v2,h2,hc2⟩ := fixed_helper_total_on_slot base a g 2#usize hcoords
    (hslots 2#usize (by decide)) (hreverse 2#usize (by decide))
  obtain ⟨v3,h3,hc3⟩ := fixed_helper_total_on_slot base a g 3#usize hcoords
    (hslots 3#usize (by decide)) (hreverse 3#usize (by decide))
  refine ⟨Array.make 4#usize [v0,v1,v2,v3], ?_, ?_⟩
  · simp only [fast_dots.four_dots_fixed, hs, hcopy, core.result.Result.unwrap,
      bind_tc_ok,h0,h1,h2,h3]
  · intro x hx
    change x ∈ [v0,v1,v2,v3] at hx
    simp only [List.mem_cons,List.mem_singleton] at hx
    rcases hx with h | h | h | h
    · subst x; exact hc0
    · subst x; exact hc1
    · subst x; exact hc2
    · subst x; exact hc3

#print axioms fixed_four_total_on_slots

#print axioms installed_old_callback_success_fixed_helper
#print axioms fixed_helper_total_on_slot
end AspisR1FastDotsInstalledReverseHelperRootV1
