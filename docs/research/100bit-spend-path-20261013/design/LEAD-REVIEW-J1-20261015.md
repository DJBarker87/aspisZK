# Lead review of the J1 relation (c7b5a949e)

Reviewed: `lean/SpendRelation.lean`, `lean/SpendRelationExtraction.lean`,
`lean/InputWitnessCheck.lean`, `lean/PublicOptionShape.lean`,
`design/J1-RELATION-STATEMENT-20261015.md`, `design/J1-SOURCE-REUSE-20261015.md`
and `evidence/j1-relation-review-20261015/`. Against: decision 1 of
`LEAD-DECISIONS-20261015.md` and `lean/AppendSemantics.lean`, `AppendPair.lean`,
`AppendPath.lean`.

## J1.R1 Accepted

The witness, the input clause (`InputWitnessCore.Relation`: valid pair,
selected slot occupied, selected commitment equals the note built from
`ownerKey sk`, first sibling is the other pair slot, nullifier, 24-step
membership at the anchor), integer conservation over `Fin (2^30)` with the
equation in ℕ, the change commitment, the variant output clause and canonical
option shape all match decision 1. `check = true ↔ Rspend` is the decidable
checker decision 3 needs, and `of_production` is the right direction of the
R0 bridge (Rspend implies `InputNoteExtracted` for the same value, so it is at
least as strong as `sourceData.paymentWitness`).

Nonnegative values are accepted as the soundness relation. Zero-valued notes
do not break conservation; the honest builder's positivity is a policy of the
prover, not a property the verifier has to deliver. The difference stays
stated in the J1 document as it is.

## J1.R2 Correction: Rspend omits the append transition

The circuit proves the append, and the pool takes the after-state from the
statement. `AppendSemantics.GateFacts` already derives, from the same
production hypotheses `of_production` uses:

- `pub.nextRoot = AppendPath.pathPrefix pub pair 20`;
- the carry frontier cell `= AppendPath.pathPrefix pub pair (digestCarry pub.nextPairIndex)` when the carry is below 20;
- `pair = nodeCompress recipient pub.change` (transfer) or `nodeCompress pub.change 0` (withdrawal).

`Rspend` as committed leaves `nextRoot` and `nextFrontier` free. A
knowledge-sound proof of it would therefore let a prover with a valid input
note choose an arbitrary next root, which is note forgery. Knowledge soundness
for Rspend alone is not the property the pool relies on.

Required change (lead-fixed statement):

```lean
def outputPair (pub : Public K) : Option (R0P.Digest K) :=
  match pub.variant with
  | .privateTransfer => pub.recipient.map (fun r => nodeCompress r pub.change)
  | .withdrawal => some (nodeCompress pub.change (fun _ => 0))

def AppendBinding (pub : Public K) : Prop :=
  ∃ pair, outputPair pub = some pair ∧
    pub.nextRoot = AppendPath.pathPrefix pub pair 20 ∧
    ∀ hc : digestCarry pub.nextPairIndex < 20,
      pub.nextFrontier ⟨digestCarry pub.nextPairIndex, hc⟩ =
        AppendPath.pathPrefix pub pair (digestCarry pub.nextPairIndex)

def Rspend (pub : Public K) (w : Witness K) : Prop :=
  <the five existing conjuncts> ∧ AppendBinding pub
```

`AppendBinding` is witness-free, so `check` gains one Boolean conjunct over
public data (`outputPair`, then `digestEqCheck` on the root and the carry cell)
and `check_eq_true_iff` is extended accordingly. `of_production` is extended
by `AppendSemantics.of_production` (`root`, `carry`, `transferPair`,
`withdrawalPair`); no new production fact is needed.

## J1.R3 Placement of the remaining append facts

These stay outside Rspend and are named obligations of the scope in decision 4,
not open-ended "settlement" items:

1. `AppendSemantics.NonCarryShape` (non-carry frontier cells) is checked by
   the program from public data (`validate_transition` on the host; the pool
   program's counterpart must be cited by file and line in the Pool-adapter
   statement-binding item). It is a program check, not a proof obligation.
2. Frozen empty-root table equals the recursively generated empty roots, and
   the chronological frontier invariant (`AppendTreeState`): tree semantics,
   release gate.
3. Freshness of the nullifier, anchor-in-history, snapshot equals the live
   state, account custody: release gate, as decided.

## J1.R4 What J1 still owes

The relation half of J1 is accepted after J1.R2. J1 is not complete. The
remaining J1 items from decision 4 are unchanged: base-field (M31) public
carrier with the descent from the extension-field `Public`; the public-byte
decoder (§9 serialisation) with its mapping to `R0P.Public` and the
canonical-option check; commitment-cut logs and views; typed prefix parsers
with prefix-extension stability; S2/private-salt configuration, row σ maps
and input-length bounds. The `R1SemanticPayloadView` bundle's missing source
hashes for `R1SemanticRecordCodec` and `R0P.MaskView` are fixed before the
J-series replay.

## J1.R5 Order

J1.R2 lands first (focused compile of `R1SpendRelation` and
`R1SpendRelationExtraction` with axioms), then the J1.R4 items, then J5 ∥ J2
as decided.
