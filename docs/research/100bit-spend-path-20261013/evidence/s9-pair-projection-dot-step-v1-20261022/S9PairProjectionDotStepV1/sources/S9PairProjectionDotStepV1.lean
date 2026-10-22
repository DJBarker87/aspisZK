import S9PairCallerStepOwnedFieldBridgeV1
import S9PairCallerStepOperationBridgeV1
import S9ConcreteArithmeticAcceptedRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9PairProjectionDotStepV1
open AspisR1S9PairCallerStepV1
abbrev Canonical (x : field.WideExact) := AspisR1S9CurrentFieldOpsV1.Canonical (toP6W x)
abbrev decode (x : field.WideExact) := AspisR1S9CurrentFieldOpsV1.decode (toP6W x)

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B)
    (v : B) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem reader_canonical (f : Slice U8) (j : Usize) (value : field.WideExact)
    (h : weights.field f j = .ok value) : Canonical value := by
  obtain ⟨owned, start, next, finish, selected, arr, howned, hmap,
    hstart, hnext, hfinish, hselected, hlen, hslice, hlimbs,
    hparser, hpacked, hcanonical⟩ :=
    AspisR1S9PairCallerStepOwnedFieldBridgeV1.pair_field_success_actual_reader
      f j value h
  exact hcanonical

/-- A successfully continued source projection step performs the actual
canonical field product and accumulation, on the same values read by that
execution. Canonical accumulator/coefficient reads remain explicit. -/
theorem continued_projection_dot_step
    (f : Slice U8) (libra : Array field.WideExact 4#usize)
    (iter iterOut : core.ops.range.Range Usize)
    (parts partsOut : Array field.WideExact 7#usize)
    (hparts : ∀ x, Array.index_usize parts 4#usize = .ok x → Canonical x)
    (hlibra : ∀ j x, Array.index_usize libra j = .ok x → Canonical x)
    (hbody : weights.Weights.pair_s2_libra_parts_projection_loop.body
      f libra iter parts = .ok (.cont (iterOut, partsOut))) :
    ∃ (j : Usize) (old value coef total : field.WideExact),
      Array.index_usize parts 4#usize = .ok old ∧
      weights.field f j = .ok value ∧
      Array.index_usize libra j = .ok coef ∧
      Array.update parts 4#usize total = .ok partsOut ∧
      Canonical value ∧ Canonical total ∧
      decode total = decode old + decode value * decode coef := by
  unfold weights.Weights.pair_s2_libra_parts_projection_loop.body at hbody
  cases hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e => simp only [hnext, bind_tc_fail] at hbody; cases hbody
  | div => simp only [hnext, bind_tc_div] at hbody; cases hbody
  | ok p =>
      rcases p with ⟨opt, iter1⟩
      cases opt with
      | none => simp only [hnext, bind_tc_ok] at hbody; cases hbody
      | some j =>
          simp only [hnext, bind_tc_ok] at hbody
          obtain ⟨old, hold, hrest⟩ := bind_success _ _ _ hbody
          obtain ⟨value, hfield, hrest⟩ := bind_success _ _ _ hrest
          obtain ⟨coef, hcoef, hrest⟩ := bind_success _ _ _ hrest
          obtain ⟨prod, hprod, hrest⟩ := bind_success _ _ _ hrest
          obtain ⟨total, htotal, hrest⟩ := bind_success _ _ _ hrest
          obtain ⟨out, hupdate, hret⟩ := bind_success _ _ _ hrest
          have hpair := ControlFlow.cont.inj (Result.ok.inj hret)
          have hout : out = partsOut := congrArg Prod.snd hpair
          rw [hout] at hupdate
          have hvalue := reader_canonical f j value hfield
          have hprodP : @AspisR1S9HelperP6.FieldOps.wideMul
              AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (toP6W value) (toP6W coef) =
              .ok (toP6W prod) := by
            simpa only [hprod, AspisR1S9PairCallerStepOperationBridgeV1.mapResult] using
              (AspisR1S9PairCallerStepOperationBridgeV1.map_wide_mul value coef).symm
          obtain ⟨hprodCan, hprodDecode⟩ :=
            AspisR1.S9ConcreteArithmeticAcceptedRootV1.wideMul_success
              (toP6W value) (toP6W coef) (toP6W prod) hvalue (hlibra j coef hcoef) hprodP
          have htotalP : @AspisR1S9HelperP6.FieldOps.wideAdd
              AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (toP6W old) (toP6W prod) =
              .ok (toP6W total) := by
            simpa only [htotal, AspisR1S9PairCallerStepOperationBridgeV1.mapResult] using
              (AspisR1S9PairCallerStepOperationBridgeV1.map_wide_add old prod).symm
          obtain ⟨htotalCan, htotalDecode⟩ :=
            AspisR1.S9ConcreteArithmeticAcceptedRootV1.wideAdd_success
              (toP6W old) (toP6W prod) (toP6W total) (hparts old hold) hprodCan htotalP
          rw [hprodDecode] at htotalDecode
          exact ⟨j, old, value, coef, total, hold, hfield, hcoef, hupdate,
            hvalue, htotalCan, htotalDecode⟩

#print axioms continued_projection_dot_step
end AspisR1S9PairProjectionDotStepV1
