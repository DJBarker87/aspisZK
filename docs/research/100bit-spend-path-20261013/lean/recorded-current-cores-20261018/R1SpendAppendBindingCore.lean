import R1AppendPathCore
import R0P.Core

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

end AspisR1.SpendRelation


set_option pp.universes true in
#check @AspisR1.SpendRelation.outputPair

#print AspisR1.SpendRelation.outputPair
#print axioms AspisR1.SpendRelation.outputPair

#print AspisR1.SpendRelation.AppendBinding
#print axioms AspisR1.SpendRelation.AppendBinding
