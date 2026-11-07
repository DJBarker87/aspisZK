import RPz8_F3U_Averaging
import RPz7_F3T_AccountCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNC_NoSecondCharge
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.CausalFirstHitUnionBound
attribute [local instance] Classical.propDecidable

/-- Both uses of the SAME E_rec are covered by one indicator. -/
theorem no_second_charge (r m : Rat) (event attack : Prop)
    (nonnegative : 0 ≤ m) (each : r ≤ m + indicator event)
    (split : attack → event) :
    max r (indicator attack) ≤ m + indicator event := by
  apply max_le each
  by_cases ha : attack
  · have he := split ha
    simp only [indicator, if_pos ha, if_pos he]
    linarith
  · simp only [indicator, if_neg ha]
    have he : 0 ≤ indicator event := by unfold indicator; split_ifs <;> norm_num
    change 0 ≤ m + indicator event
    exact add_nonneg nonnegative he

/-- Unconditional averaging over every oracle H. `attack` observes its own
program output; there is no Realizes predicate, conditioning or support filter
in the measured loss. This is the generic averaging fold, not native inclusion. -/
theorem average {A B C : Type}
    (execution : Program Bytes State A) (runtime : Program Bytes State B)
    (model : Program Bytes State C) (mass : View Bytes State B → Rat)
    (failure : View Bytes State C → Rat) (attack : View Bytes State A → Prop)
    {X : Type} (source : Program Bytes State X)
    (project : X → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : X → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat) (budget : ∀ H, firstReads emptyTable (eval H source).1 ≤ Q+1921)
    (nonnegative : ∀ H, 0 ≤ failure (eval H model))
    (each : ∀ H, mass (eval H runtime) ≤ failure (eval H model) +
      indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
        (eval H (Hiq_RecordedJoint.program source project select))))
    (split : ∀ H, attack (eval H execution) →
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
        (eval H (Hiq_RecordedJoint.program source project select))) :
    lazyMean (F3U_Joint.program runtime execution model) emptyTable
      (fun v => max (mass v.2.1) (indicator (attack v.2.2.1))) ≤
    lazyMean model emptyTable failure + F3T_Numeric.accountLoss Q := by
  let joint := F3U_Joint.program runtime execution model
  have pointwise : ∀ H, (fun v => max (mass v.2.1) (indicator (attack v.2.2.1)))
      (eval H joint) ≤ failure (eval H model) +
      indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
        (eval H (Hiq_RecordedJoint.program source project select))) := by
    intro H
    simp only [joint,F3U_Joint.output]
    exact no_second_charge _ _ _ _ (nonnegative H) (each H) (split H)
  have averaged := F3U_Averaging.charge joint model
    (Hiq_RecordedJoint.program source project select)
    (fun v => max (mass v.2.1) (indicator (attack v.2.2.1))) failure
    (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)) pointwise
  exact averaged.trans (add_le_add (le_refl _) (F3T_AccountCharge.bound source project select Q budget))

#print axioms no_second_charge
#print axioms average
end AspisR1.NNC_NoSecondCharge
