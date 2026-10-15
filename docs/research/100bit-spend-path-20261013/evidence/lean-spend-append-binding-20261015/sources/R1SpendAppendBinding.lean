import R1InputWitnessCheck
import R1AppendPath

/-! Public output-pair, new-root and carry-frontier binding required by J1.R2.
The recurrence is the circuit's literal frozen-table recurrence. Non-carry
frontier validation and the chronological tree invariant are separate. -/
set_option autoImplicit false
namespace AspisR1.SpendRelation
open R0P
variable {K : Type} [Field K] [DecidableEq K]

def outputPair (pub : Public K) : Option (Digest K) :=
  match pub.variant with
  | .privateTransfer => pub.recipient.map (fun r => nodeCompress r pub.change)
  | .withdrawal => some (nodeCompress pub.change (fun _ => 0))

def AppendBinding (pub : Public K) : Prop :=
  ∃ pair, outputPair pub = some pair ∧
    pub.nextRoot = AppendPath.pathPrefix pub pair 20 ∧
    ∀ hc : digestCarry pub.nextPairIndex < 20,
      pub.nextFrontier ⟨digestCarry pub.nextPairIndex, hc⟩ =
        AppendPath.pathPrefix pub pair (digestCarry pub.nextPairIndex)

def appendCheck (pub : Public K) : Bool :=
  match outputPair pub with
  | none => false
  | some pair =>
      InputWitnessCheck.digestEqCheck pub.nextRoot (AppendPath.pathPrefix pub pair 20) &&
        if hc : digestCarry pub.nextPairIndex < 20 then
          InputWitnessCheck.digestEqCheck
            (pub.nextFrontier ⟨digestCarry pub.nextPairIndex, hc⟩)
            (AppendPath.pathPrefix pub pair (digestCarry pub.nextPairIndex))
        else true

theorem appendCheck_eq_true_iff (pub : Public K) :
    appendCheck pub = true ↔ AppendBinding pub := by
  cases hp : outputPair pub with
  | none => simp [appendCheck, AppendBinding, hp]
  | some pair =>
      by_cases hc : digestCarry pub.nextPairIndex < 20
      · simp [appendCheck, AppendBinding, hp, hc,
          InputWitnessCheck.digestEqCheck_eq_true_iff]
      · simp [appendCheck, AppendBinding, hp, hc,
          InputWitnessCheck.digestEqCheck_eq_true_iff]

#print axioms appendCheck_eq_true_iff
end AspisR1.SpendRelation
