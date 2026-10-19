import ExtractedSemanticRoundsCheckedTrace
import ExtractedVerifyFinishReachability

/-! Composition point for the concrete extracted semantic verifier: successful
finish execution gives a successful rounds call, and the checked-trace theorem
turns that exact call into the ten source-level row checks. This is not yet a
bridge to LiteralAcceptanceTerminal.Checks or the abstract byte-protocol
decision function. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1PublicPreparation.RawFinishCheckedSemanticRuns

theorem finish_success_checked_rounds
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (before : r1_wire.SemanticTranscript H)
    (challenges : r1_wire.Challenges)
    (obs : Option (AspisR1PublicPreparation.verifier.Phase → Result Unit))
    (out : AspisR1PublicPreparation.r1_semantic.Verified H)
    (hfinish : FinishModel.finish R B D pub pre before challenges obs =
      ok (.Ok out)) :
    ∃ running afterRounds,
      RoundModel.rounds R D pre before = ok (.Ok (running, out.alpha, afterRounds)) ∧
      ∃ (record : r1_wire.ValidatedRecord)
        (decoded : Array aspis_core.field.QM31 1#usize) (initial : aspis_core.field.QM31),
        r1_wire.Prefix.validated_record pre 14#u8 = ok (.Ok record) ∧
        R.decode 1#usize record 0#usize = ok (.Ok decoded) ∧
        Array.index_usize decoded 0#usize = ok initial ∧
        SemanticRoundsCheckedTrace.CheckedRun R D pre SemanticRoundsCheckedTrace.schedule
          (initial, Array.repeat 10#usize aspis_core.field.QM31.ZERO, before)
          (running, out.alpha, afterRounds) := by
  obtain ⟨running, afterRounds, _record25, _record26, _z0, _t26, _z1, _t27,
      hrounds, _hchallenges, _hstate, _htranscript, _hclaims, _hrecord25,
      _hextra, _hc25, _hrecord26, _hbeforeZ1, _hc26, _hz⟩ :=
    FinishCalls.finish_success R B D pub pre before challenges obs out hfinish
  exact ⟨running, afterRounds, hrounds,
    SemanticRoundsCheckedTrace.rounds_checked_success R D pre before afterRounds
      running out.alpha hrounds⟩

#print axioms finish_success_checked_rounds

end AspisR1PublicPreparation.RawFinishCheckedSemanticRuns
