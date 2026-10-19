import ExtractedTx1Reachability
import AspisR1HeapFilledOverwriteTx1.Funs
import HeapFilledOverwriteTx1CandidateSuccessV1
import Tx1FinalLenBoundV8
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace Tx1AccumulatorOverwriteCandidateV1

open AspisR1PublicPreparation

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Isolated source candidate for the single Accumulator::new callsite change:
    the original `heap::filled` call is replaced by the extracted
    `heap::filled_overwrite` candidate. No production source is edited. -/
noncomputable def newAccumulatorOverwrite (v : transport.Variant) :
    Result (core.result.Result verifier.Accumulator verifier.Error) := do
  let n ← Tx1Model.final_len v
  let r ← AspisR1HeapFilledOverwriteTx1.aspis_core.r0.heap.filled_overwrite
    Tx1Model.copyInst n aspis_core.field.QM31.ZERO
  let r1 ← core.result.Result.map_err Tx1Model.allocationErrorClosure r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ok (core.result.Result.Ok
      { weights := val, rhs := aspis_core.field.WideExact.ZERO,
        power := Tx1Model.one, next := 0#usize })
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      verifier.Accumulator (core.convert.FromSame verifier.Error) residual

/-- Install exactly the candidate helper at the original Tx1 boundary slot;
    all other abstract Tx1 boundaries are unchanged. -/
noncomputable def withOverwriteFilled
    (B : Tx1Model.Boundaries) : Tx1Model.Boundaries :=
  { B with filled := AspisR1HeapFilledOverwriteTx1.aspis_core.r0.heap.filled_overwrite }

theorem source_callsite_eq_candidate (B : Tx1Model.Boundaries)
    (v : transport.Variant) :
    Tx1Model.newAccumulator (withOverwriteFilled B) v = newAccumulatorOverwrite v := by
  rfl

theorem overwrite_constructor_success
    (v : transport.Variant) (out : verifier.Accumulator)
    (h : newAccumulatorOverwrite v = .ok (.Ok out)) :
    out.weights.length ≤ 256 ∧
      ∀ i : Usize, i.val < out.weights.length →
        Slice.index_usize (out.weights : Slice aspis_core.field.QM31) i =
          .ok aspis_core.field.QM31.ZERO := by
  unfold newAccumulatorOverwrite at h
  obtain ⟨n, hn, h⟩ := bind_success _ _ _ h
  -- The constructor's result is a successful filled_overwrite call.
  obtain ⟨r, hr, h⟩ := bind_success _ _ _ h
  cases r with
  | Err e =>
    simp only [core.result.Result.map_err, Tx1Model.allocationErrorClosure,
      Tx1Model.allocationError, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h
  | Ok weights =>
    simp only [core.result.Result.map_err, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch] at h
    have hout : out = ⟨weights, aspis_core.field.WideExact.ZERO,
        Tx1Model.one, 0#usize⟩ := (core.result.Result.Ok.inj (Result.ok.inj h)).symm
    rw [hout]
    have hcontents := HeapFilledOverwriteTx1CandidateSuccessV1.filled_success_contents
      Tx1Model.copyInst n aspis_core.field.QM31.ZERO weights hr
    constructor
    · have hnle : n.val ≤ 256 := by
        cases v <;>
          simp only [Tx1FinalLenBoundV6.final_len_cases, Result.ok.injEq] at hn <;>
          rw [← hn] <;> simp only [UScalar.ofNatCore_val_eq] <;> omega
      rw [hcontents.1]
      exact hnle
    · intro i hi
      exact hcontents.2 i (by simpa [hcontents.1] using hi)

#print axioms overwrite_constructor_success
#print axioms source_callsite_eq_candidate
end Tx1AccumulatorOverwriteCandidateV1
