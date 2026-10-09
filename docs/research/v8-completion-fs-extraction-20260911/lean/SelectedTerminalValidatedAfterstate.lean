import SelectedTerminalPublicContext

/-!
# Validated public context to selected afterstate semantics

This leaf discharges the static public comparison and carry-control premises
of the existing selected afterstate theorem from the executable,
source-shaped `validateTransition` check.  The semantic table equations,
Poseidon constraints, and weighted-copy aliases remain genuine arithmetic
premises; they are not inferred from public validation.

No terminal acceptance or literal Rust refinement is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.SelectedTerminalValidatedAfterstate

open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticAfterstateChecks
open AspisV8.SelectedSemanticTransfer
open AspisV8.SelectedSemanticOutputTransition
open AspisV8.SelectedNoteRecovery
open AspisV8.SelectedCopyAliases
open AspisV8.EarlyC1CopyCollision
open SelectedTerminalPublicContext

noncomputable section

/-- The carry derived from the live transition is the carry used by the
projected semantic public input.  Neither side is prover supplied. -/
theorem carryIndexOf_eq_publicProjection (pub : TransferPublicInput)
    (transition : TransitionInput) :
    carryIndexOf transition =
      AspisV8.SelectedAppendAfterstate.carryIndex
        (publicProjection pub transition).appendIndex := by
  change AspisV8.SelectedAppendAfterstate.carryIndex
      transition.live.nextPairIndex =
    AspisV8.SelectedAppendAfterstate.carryIndex
      transition.live.nextPairIndex
  rfl

/-- Successful source-shaped public validation plus the actual selected
semantic row equations constructs the complete afterstate record.  This is
the old V7/V8 bridge with `SourceComparisons` and `carryExact` removed from
the caller interface. -/
theorem afterstate_checks_from_validated_transition
    (pub : TransferPublicInput) (transition : TransitionInput)
    (t : BaseTable)
    (validated : validateTransition pub transition = true)
    (vanish : RowsVanish (publicProjection pub transition) t) :
    AspisV8.SelectedAppendAfterstate.AfterstateChecks t
      transition.live.sequence
      (publicProjection pub transition).appendIndex
      transition.after.nextPairIndex
      (AspisV8.SelectedSemanticOutputTransition.extend20 emptyRoot)
      (AspisV8.SelectedSemanticOutputTransition.extend20
        (publicProjection pub transition).frontier)
      (AspisV8.SelectedSemanticOutputTransition.extend20
        (publicProjection pub transition).nextFrontier)
      (publicProjection pub transition).nextRoot := by
  exact afterstate_checks
    (publicProjection pub transition) t
    transition.live.sequence transition.after.nextPairIndex
    (carryIndexOf transition) vanish
    (validateTransition_sourceComparisons pub transition validated)
    (carryIndexOf_eq_publicProjection pub transition)

/-- In particular, the proposed-root binding is obtained from the SAME
semantic table.  It is not a caller-supplied digest-control premise. -/
theorem validated_root_binding
    (pub : TransferPublicInput) (transition : TransitionInput)
    (t : BaseTable)
    (validated : validateTransition pub transition = true)
    (vanish : RowsVanish (publicProjection pub transition) t)
    (limb : Fin 8) :
    t 859 limb.val - (publicProjection pub transition).nextRoot limb = 0 := by
  exact (afterstate_checks_from_validated_transition
    pub transition t validated vanish).rootBinding limb

#print axioms carryIndexOf_eq_publicProjection
#print axioms afterstate_checks_from_validated_transition
#print axioms validated_root_binding

end
end AspisV8Completion.SelectedTerminalValidatedAfterstate
