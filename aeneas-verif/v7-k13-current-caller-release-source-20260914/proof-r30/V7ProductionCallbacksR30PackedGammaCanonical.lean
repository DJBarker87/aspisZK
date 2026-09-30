import V7ProductionCallbacksR30GammaHelpersCanonical

/-! Packed source gamma output with both successful decoder certificates. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ProductionCallbacksR30PackedGammaCanonical
open V7ProductionCallbacksR30MutableCanonical
open V7ProductionCallbacksR30GammaC1Canonical
open V7ProductionCallbacksR30GammaHelpersCanonical
open V7ProductionCallbacksR30PackedDecoderCanonical
open V7CallerCurrentReleaseR26FieldBridge

local instance : Inhabited V7ProductionCallbacksR30Qm31Canonical.CallbackQM31 :=
  ⟨V7ProductionCallbacksR29.aspis_core.field.QM31.ZERO⟩

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do let value ← input; next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

def DecoderCertificate (c1Packed c2Packed : Slice Std.U8) : Prop :=
  ∃ c1 : Array Std.U32 104#usize, ∃ c2 : Array Std.U32 48#usize,
    V7ProductionCallbacksR29.aspis_core.v6_onefold.decode_packed_m31_eight_aligned
      104#usize c1Packed = ok (.Ok c1) ∧ WordsCanonical c1 ∧
    V7ProductionCallbacksR29.aspis_core.v6_onefold.decode_packed_m31_eight_aligned
      48#usize c2Packed = ok (.Ok c2) ∧ WordsCanonical c2

theorem successful_packed_gamma_canonical
    (c1Packed c2Packed : Slice Std.U8)
    (powers : V7ProductionCallbacksR29.aspis_core.state_only_spend_query.StateOnlySpendQueryPowers)
    (output : Helper)
    (run : V7ProductionCallbacksR29.aspis_core.v6_onefold.gamma_combine_v6_packed_layer0
      c1Packed c2Packed powers = ok (.Ok output)) :
    SliceAll GeneratedCanonicalQM31 output.to_slice ∧ DecoderCertificate c1Packed c2Packed := by
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.gamma_combine_v6_packed_layer0 at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨c1Length, c1LengthRun, run⟩ := run
  split at run
  · cases run
  · rw [bind_eq_ok_iff] at run
    obtain ⟨c2Length, c2LengthRun, run⟩ := run
    split at run
    · cases run
    · rw [bind_eq_ok_iff] at run
      obtain ⟨c1Result, c1Run, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨c1Branch, c1BranchRun, run⟩ := run
      cases c1Result with
      | Err error =>
          have branchExact : c1Branch = .Break (.Err error) := by
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using (Result.ok.inj c1BranchRun).symm
          rw [branchExact] at run
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
      | Ok c1 =>
          have c1Canonical := successful_packed_decoder_canonical 104#usize c1Packed c1 c1Run
          have branchExact : c1Branch = .Continue c1 := by
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using (Result.ok.inj c1BranchRun).symm
          rw [branchExact] at run
          simp only at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨combined, combinedRun, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨power0, power0Run, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨power1, power1Run, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨c2Result, c2Run, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨c2Branch, c2BranchRun, run⟩ := run
          cases c2Result with
          | Err error =>
              have branchExact : c2Branch = .Break (.Err error) := by
                simpa [core.result.Result.Insts.CoreOpsTry.branch] using (Result.ok.inj c2BranchRun).symm
              rw [branchExact] at run
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at run
          | Ok c2 =>
              have c2Canonical := successful_packed_decoder_canonical 48#usize c2Packed c2 c2Run
              have branchExact : c2Branch = .Continue c2 := by
                simpa [core.result.Result.Insts.CoreOpsTry.branch] using (Result.ok.inj c2BranchRun).symm
              rw [branchExact] at run
              simp only [Array.to_slice_mut, Std.lift, core.slice.Slice.iter_mut,
                core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate, bind_tc_ok] at run
              rw [bind_eq_ok_iff] at run
              obtain ⟨finished, loopRun, run⟩ := run
              have combinedCanonical := callback_c1_gamma_canonical c1 powers combined combinedRun
              have finishedCanonical := successful_helper_population_canonical _ _ _ combined
                _ c2 _ (fun e => e) finished combinedCanonical loopRun
              have outputExact := core.result.Result.Ok.inj (Result.ok.inj run)
              exact ⟨outputExact ▸ finishedCanonical,
                ⟨c1, c2, c1Run, c1Canonical, c2Run, c2Canonical⟩⟩

#print axioms successful_packed_gamma_canonical
end V7ProductionCallbacksR30PackedGammaCanonical
