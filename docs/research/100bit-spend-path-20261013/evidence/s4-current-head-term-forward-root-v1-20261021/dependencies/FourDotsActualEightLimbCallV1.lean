import FourDotsActualInnerLoopBoundV1
import FourDotsWideLimbCanonicalV1
import FourDotsBatchInnerCallsV1
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsActualEightLimbCallV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Usize := Std.Usize
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev Range := core.ops.range.Range Usize
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev StepBy := AspisR1FastDotsBatchBodyAdvance.StepBy

/-- The current Rust source defines `WideExact::LIMB_COUNT` as 8.  The
    generated Ops record represents that constant as an explicit result-valued
    call; this adapter pins that slot to the source constant. -/
def withCurrentLimbCount8 (ops : Ops) : Ops :=
  { ops with wideLimbCount := .ok 8#usize }

/-- Bind both source constants/conversions used by the actual term body:
    `WideExact::LIMB_COUNT = 8` and its current `to_limbs` implementation. -/
def withCurrentWideOps (ops : Ops) : Ops :=
  { (withCurrentLimbCount8 ops) with
    wideToLimbs := AspisR1EbyKPushWideToQ.toLimbs }

theorem current_limb_count_slot (ops : Ops) :
    (withCurrentLimbCount8 ops).wideLimbCount = .ok 8#usize := rfl

theorem eight_limb_inner_loop_success_global_bound
    (ops : Ops) (iter : Range) (sums out : Array U64 8#usize)
    (scalar : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (coeff : Array Std.U32 8#usize)
    (hcoeff : ∀ i : Fin 8,
      (coeff.val[i.val]'(by simpa [coeff.property] using i.isLt)).val < 2147483647)
    (hbase4 : ∀ i : Fin 8,
      AspisR1FastDotsActualLimbPrefixStepV3.cell sums i ≤ 4 * AspisR1FastDotsActualLimbPrefixStepV3.cap)
    (hsuffix : ∀ i : Fin 8, iter.start.val ≤ i.val →
      AspisR1FastDotsActualLimbPrefixStepV3.cell sums i ≤ 3 * AspisR1FastDotsActualLimbPrefixStepV3.cap)
    (hscalar : scalar.val < 2147483647)
    (hloop : AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0_loop0
      (withCurrentLimbCount8 ops) iter sums scalar coeff = .ok out) :
    ∀ i : Fin 8,
      AspisR1FastDotsActualLimbPrefixStepV3.cell out i ≤ 4 * AspisR1FastDotsActualLimbPrefixStepV3.cap := by
  exact AspisR1FastDotsActualInnerLoopBoundV1.inner_loop_success_global_bound
    (withCurrentLimbCount8 ops) iter sums out scalar coeff hcoeff hbase4 hsuffix hscalar hloop

/-- The coefficient bound needed by the emitted limb loop follows directly
    from the exact eight-coordinate `WideExact::to_limbs` body, provided the
    source Wide value is canonical in its eight M31 coordinates. -/
theorem current_wide_coefficients_canonical
    (x : Wide) (hx : AspisR1FastDotsWideLimbCanonical.CoordinateBound x)
    (coeff : Array Std.U32 8#usize)
    (hcall : AspisR1EbyKPushWideToQ.toLimbs x = .ok coeff) :
    ∀ i : Fin 8,
      (coeff.val[i.val]'(by simpa [coeff.property] using i.isLt)).val < 2147483647 := by
  have hcoeff : coeff = AspisR1FastDotsWideLimbCanonical.limbArray x :=
    Result.ok.inj (hcall.symm.trans
      (AspisR1FastDotsWideLimbCanonical.toLimbs_actual_value x))
  subst coeff
  exact AspisR1FastDotsWideLimbCanonical.all_emitted_limb_entries_canonical x hx

/-- The global bound theorem specialized to coefficients returned by the
    current `WideExact::to_limbs`. The input coordinate-canonicality premise
    and scalar-canonicality premise are retained explicitly. -/
theorem current_wide_inner_loop_success_global_bound
    (ops : Ops) (x : Wide) (hx : AspisR1FastDotsWideLimbCanonical.CoordinateBound x)
    (iter : Range) (sums out : Array U64 8#usize)
    (scalar : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (coeff : Array Std.U32 8#usize)
    (hcall : (withCurrentWideOps ops).wideToLimbs x = .ok coeff)
    (hbase4 : ∀ i : Fin 8,
      AspisR1FastDotsActualLimbPrefixStepV3.cell sums i ≤ 4 * AspisR1FastDotsActualLimbPrefixStepV3.cap)
    (hsuffix : ∀ i : Fin 8, iter.start.val ≤ i.val →
      AspisR1FastDotsActualLimbPrefixStepV3.cell sums i ≤ 3 * AspisR1FastDotsActualLimbPrefixStepV3.cap)
    (hscalar : scalar.val < 2147483647)
    (hloop : AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0_loop0
      (withCurrentWideOps ops) iter sums scalar coeff = .ok out) :
    ∀ i : Fin 8,
      AspisR1FastDotsActualLimbPrefixStepV3.cell out i ≤ 4 * AspisR1FastDotsActualLimbPrefixStepV3.cap := by
  have hcoeff := current_wide_coefficients_canonical x hx coeff hcall
  exact AspisR1FastDotsActualInnerLoopBoundV1.inner_loop_success_global_bound
    (withCurrentWideOps ops) iter sums out scalar coeff hcoeff hbase4 hsuffix hscalar hloop

/-- Successful actual emitted batch-body execution, with the exact Rust
    `LIMB_COUNT` value bound into the Ops slot, selects a reduction loop over
    precisely the eight limbs. This transports the successful term call and
    inner-loop call from the complete generated batch body. -/
theorem batch_body_success_uses_eight_limb_reduction
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (iter it' : StepBy) (limbs limbs' : Array U64 8#usize)
    (hbody : AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
      (withCurrentLimbCount8 ops) a a1 slot iter limbs = .ok (.cont (it', limbs'))) :
    ∃ start batchEndArg rangeEnd sums1,
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter =
          .ok (some start, it') ∧
      UScalar.add start 4#usize = .ok batchEndArg ∧
      core.cmp.min core.cmp.OrdUsize batchEndArg 26#usize = .ok rangeEnd ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0
        (withCurrentLimbCount8 ops) { start, «end» := rangeEnd } a a1 slot
        (Array.repeat 8#usize 0#u64) = .ok sums1 ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
        (withCurrentLimbCount8 ops) { start := 0#usize, «end» := 8#usize }
        limbs sums1 = .ok limbs' := by
  obtain ⟨start, batchEndArg, rangeEnd, sums1, limbCount, hnext, hadd, hmin,
      hterms, hcount, hlimbs⟩ :=
    AspisR1FastDotsBatchInnerCalls.body_success_cont_inner_calls
      (withCurrentLimbCount8 ops) a a1 slot iter it' limbs limbs' hbody
  have hcount' : limbCount = 8#usize := by
    change Result.ok 8#usize = Result.ok limbCount at hcount
    exact (Result.ok.inj hcount).symm
  subst limbCount
  exact ⟨start, batchEndArg, rangeEnd, sums1, hnext, hadd, hmin, hterms, hlimbs⟩

#print axioms current_limb_count_slot
#print axioms eight_limb_inner_loop_success_global_bound
#print axioms current_wide_coefficients_canonical
#print axioms current_wide_inner_loop_success_global_bound
#print axioms batch_body_success_uses_eight_limb_reduction

end AspisR1FastDotsActualEightLimbCallV1
