import S4ReverseWholeHelperRootV1

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

#print axioms installed_old_callback_success_fixed_helper
#print axioms fixed_helper_total_on_slot
end AspisR1FastDotsInstalledReverseHelperRootV1
