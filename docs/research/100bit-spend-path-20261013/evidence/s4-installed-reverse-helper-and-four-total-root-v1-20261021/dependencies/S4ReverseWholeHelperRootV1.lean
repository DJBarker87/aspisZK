import S4WholeHelperTransferRootV1
import S4LiteralN8TotalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsReverseWholeHelperRootV1
open AspisR1FastDotsCurrent
open AspisR1FastDotsWholeHelperTransferRootV1
open AspisR1FastDotsFixedTailProgramEqualityRootV1
open AspisR1FastDotsLiteralN8PackingRootV1 (literalEight)
open AspisR1FastDotsLiteralN8TotalV1 (withReducer literal_eight_success_same_p6_output)

private theorem bind_ok_inv {A B : Type} {r : Result A} {f : A → Result B} {x : B}
    (h : (r >>= f) = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Structural reverse transfer of the complete helper. The reverse head
success law is an explicit dependency, to be instantiated by the separate
old-loop reversal proof; this theorem alone does not establish that law. -/
theorem old_callback_success_fixed_helper
    (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (out : Wide)
    (hreducer : withReducer ops = ops)
    (harray : ∀ limbs : Array U64 8#usize,
      ops.arrayFromFn 8#usize
        (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops)
        limbs = AspisR1FromFnP6Generated.arrayFromFnP6 8#usize
          (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops) limbs)
    (hreverse : ∀ (iter : StepBy) (limbs result : Array U64 8#usize),
      iter.step_by = 4#usize →
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
        ops iter q g slot limbs = .ok result →
      fast_dots.four_dots_one_loop0 ops iter q g slot limbs = .ok result)
    (hrun : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      ops (q,g) slot = .ok (out,(q,g))) :
    fast_dots.four_dots_one ops q g slot = .ok out := by
  rw [old_callback_eq_grouped] at hrun
  unfold groupedOld at hrun
  obtain ⟨iter,hiter,hrun⟩ := bind_ok_inv hrun
  obtain ⟨limbs,hlimbs,hrun⟩ := bind_ok_inv hrun
  obtain ⟨values,hvalues,hrun⟩ := bind_ok_inv hrun
  obtain ⟨o,ho,hrun⟩ := bind_ok_inv hrun
  obtain ⟨value,hvalue,htail⟩ := bind_ok_inv hrun
  have hstep : iter.step_by = 4#usize := by
    simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
      core.iter.traits.iterator.Iterator.step_by.default] at hiter
    cases Result.ok.inj hiter
    rfl
  have hhead := hreverse iter (Array.repeat 8#usize 0#u64) limbs hstep hlimbs
  have hp6 := (harray limbs).symm.trans hvalues
  have hp6' : AspisR1FromFnP6Generated.arrayFromFnP6 8#usize
      (AspisR1FastDotsLiteralN8PackingRootV1.InnerFn (withReducer ops)) limbs = .ok values := by
    simpa only [hreducer] using hp6
  have hpack : literalEight ops limbs = .ok values := by
    simpa only [hreducer] using literal_eight_success_same_p6_output ops limbs values hp6'
  rw [old_captured_tail_eq_map] at htail
  obtain ⟨tailOut,htailOld,hpair⟩ := bind_ok_inv htail
  have heq : tailOut = out := congrArg Prod.fst (Result.ok.inj hpair)
  subst tailOut
  have htailFixed : fixedTail ops q g slot value = .ok out :=
    (fixed_tail_eq_old_tail ops q g slot value).trans htailOld
  rw [fixed_helper_eq_grouped]
  unfold groupedFixed
  simp only [hiter,bind_tc_ok,hhead,hpack,ho,hvalue,htailFixed]

#print axioms old_callback_success_fixed_helper
end AspisR1FastDotsReverseWholeHelperRootV1
