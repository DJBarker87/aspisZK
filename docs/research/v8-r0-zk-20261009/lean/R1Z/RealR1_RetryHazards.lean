import R1Z.RealR1_ReachableRetry
import R1Z.SideChannelRetryLaw
import R1Z.SideChannelEntropy

/-! Connect the real outer control to the existing ordered attempt record and
history-conditioned hazards. Event production and joint real/ideal trace laws
remain explicit obligations. Equality of erased outcomes does not certify the
event list, or imply a witness-independent retry probability. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.RealR1_RetryHazards
open Aeneas Aeneas.Std Result AspisR1PublicNonce41
open ProverCommitRetry34 RealR1_OuterOwner RealR1_ReachableRetry

theorem selected_trace {Extra Proof : Type} (pub : Pub)
    (nonce : NoncePolicy Extra) (schedule : ProverCommitLedger36.Schedule)
    (tape : Nat → owner.Raw) (unix : Bool) (pre : Prefix Extra) (body : Body Extra Proof)
    (records : SideChannelL1AttemptRecord.Owner (Store Extra) Proof)
    (Inv : Nat → Store Extra → Prop)
    (erasure : ∀ index s, index < 8 → Inv index s →
      realAttempt pub (nativeEntropy nonce schedule tape) (reserved pre schedule unix body) index s =
        ok ((records index s).1.result,(records index s).2))
    (advance : ∀ index s after, index < 8 → Inv index s →
      SideChannelL1AttemptRecord.eraseOwner records index s = ok (.retry,after) →
      Inv (index+1) after)
    (s : Store Extra) (initial : Inv 0 s) :
    selected true pub (nativeEntropy nonce schedule tape) (reserved pre schedule unix body) s =
      ok ((SideChannelL1AttemptRecord.run records 8 0 s).1.result,
          (SideChannelL1AttemptRecord.run records 8 0 s).2) := by
  exact (run_reachable _ (SideChannelL1AttemptRecord.eraseOwner records) Inv
    erasure advance 8 0 s (by omega) initial).trans
      (SideChannelL1AttemptRecord.erase_run records 8 0 s)

/-- Genuine conditional hazard for actual entered attempt positions. All
randomness, adversarial schedules and retained histories can be in Sample;
there is no fixed success rate or independence premise. A native record
producer must be supplied before interpreting records as native observations. -/
theorem entered_abort_hazard {Sample S Proof : Type} [Fintype Sample]
    (records : Sample → SideChannelL1AttemptRecord.Owner S Proof)
    (initial : Sample → S) (k : Fin 8) (e : ProverCommitRetry34.Error) :
    SideChannelRetryLaw.mass (fun r =>
      (k.val < (SideChannelL1AttemptRecord.run (records r) 8 0 (initial r)).1.attempts.length) ∧
      SideChannelRetryLaw.E records initial (k.val+1) e r) =
    SideChannelRetryLaw.mass (SideChannelRetryLaw.C records initial (k.val+1)) *
      SideChannelRetryLaw.hazard (SideChannelRetryLaw.C records initial (k.val+1))
        (SideChannelRetryLaw.E records initial (k.val+1) e) := by
  have same : (fun r =>
      (k.val < (SideChannelL1AttemptRecord.run (records r) 8 0 (initial r)).1.attempts.length) ∧
      SideChannelRetryLaw.E records initial (k.val+1) e r) =
      (fun r => SideChannelRetryLaw.C records initial (k.val+1) r ∧
        SideChannelRetryLaw.E records initial (k.val+1) e r) := by
    funext r
    apply propext
    exact and_congr (by
      simpa only [SideChannelRetryLaw.C,Nat.add_sub_cancel] using
        SideChannelRetryLaw.actual_entry_iff (records r) (initial r) k) Iff.rfl
  rw [same]
  exact SideChannelRetryLaw.abort_hazard records initial k e

/-- Seed-pair permutations preserve the complete entropy prefix state,
including all successful/rejected draw counts, on every byte-blind schedule.
E1 is needed separately to turn the permutation into a distribution coupling. -/
theorem entropy_count_state (e : ProverCommitPublicNonce40.Private ≃ ProverCommitPublicNonce40.Private)
    (nonce : ProverCommitLedger36.Path) (schedule : ProverCommitLedger36.Schedule)
    (tape : Nat → ProverCommitPublicNonce40.Raw) (s : LedgerState) :
    (ProverCommitPublicNonce40.generate nonce schedule
      (fun n => SideChannelEntropy.lift e (tape n)) s).2 =
    (ProverCommitPublicNonce40.generate nonce schedule tape s).2 :=
  SideChannelEntropy.count_history_preserved e nonce schedule tape s

#print axioms selected_trace
#print axioms entered_abort_hazard
#print axioms entropy_count_state
end R1Z.RealR1_RetryHazards
