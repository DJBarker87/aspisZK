import FJg_ReaderScalarCanon
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_ReadKCut
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem reached {T : Type} (r : verifier.Reader)
    (next : aspis_core.field.QM31 → verifier.Reader → Result (core.result.Result T verifier.Error))
    (out : T) (run : CheckpointBytes4Ops.withK CheckpointBytes3Reader.readK r next=ok (.Ok out)) :
    ∃ q last,CheckpointBytes3Reader.readK r=ok (.Ok q,last) ∧
      FJg_ReaderScalarCanon.CanonK q ∧ next q last=ok (.Ok out) := by
  unfold CheckpointBytes4Ops.withK at run
  obtain ⟨⟨value,last⟩,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases value with
  | Err e => cases run
  | Ok q => exact ⟨q,last,hr,FJg_ReaderScalarCanon.k r last q hr,run⟩
#print axioms reached
end AspisR1.FJg_ReadKCut
end
