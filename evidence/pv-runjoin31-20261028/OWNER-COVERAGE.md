# Exact canonical-route coverage — checked

**Owner sentence:** On the canonical-route preparation family, the universal
V152–V154 honest-family certificate covers exactly the admitted pairs prepared
by that route: the snapshot codec succeeds, the frozen outer wrapper succeeds,
and the inner compiler succeeds on the checked arguments. Every such successful
preparation yields HonestInput without a residual semantic-admission hypothesis.
Positive change is necessary for transfers and withdrawals; the complete
readiness predicates, including all remaining guards, determine this domain.

`PV_RunJoin_CanonicalCoverage31.transfer_iff` and `withdrawal_iff` (44650) prove
both directions between the actual prepared-and-honest domain and
`PV_RunJoin_CodecComposition30.Path` followed by `OuterReady30.TransferReady` or
`WithdrawalReady`. These readiness predicates were already characterized in
CanonicalReady30, with the rejection/error paths in the runjoin30 evidence.
The new equivalences do not assume that the prepared output is honest.

`PV_RunJoin_CanonicalHonest31.transfer` and `withdrawal` (44649) prove:
for every bytes/public/witness/context tuple and every returned snapshot/compiled
payload, successful canonical preparation implies a native lane-root result and
HonestInput of exactly the associated input carrying that returned payload.
HonestInput retains semantic Admission, the complete inner compiler return with
both Result layers, Checked and canonical frontier words. Input membership,
pair validity/spendability, nullifier, output commitment/amount, append root/carry,
and the private-transfer change sentinel are derived, not assumed.

The generic V152 public_eq, V153 build_eq and V154 transport_eq are the unchanged
universal theorems in HonestIdentification26. Restricting that family to these
canonical preparations requires no further admission proof. This statement is
about the canonical-route family, not a claim that all mathematical RspendPlus
pairs pass every native preparation guard. The raw noncanonical-frontier wrapper
finding and zero-change rejection findings remain recorded and unchanged.

## Premise accounting

Before: successful canonical preparation plus each semantic clause in
HonestyResidual30.Remaining was needed to obtain HonestInput. After: successful
canonical preparation alone yields HonestInput. The four residual semantic
clauses have been discharged for this family, with the same carrier, returned
payload and success event. No new T field, weakened observer or changed simulator.
The lane-root native link retains its structural (K-1 substitute) evidence class
and4096 finite complete-Result comparisons; it is not relabelled as Kani.

No deployed endpoint field was removed, added, weakened or changed (0/0/0/0).
PV_Src_Premises remains five fields. No ledger row is subtracted from the inherited
recount merely from this producer-family reachability result. V038/V045 native
execution/observation work starts only after this checked coverage stage.
The privacy target is not yet established.

All new accepted theorem axiom sets are subsets of propext/Classical.choice/
Quot.sound. Exact targets, exits, host/transport times, RSS, swap, source revisions,
blobs/hashes and axioms are retained per receipt. Caps unchanged; all swap counts0.
No shipped implementation, protocol parameter, release ELF, key, observer or
simulator was changed. No full frozen release replay is claimed by this stage.

Final preflight qualification: the canonical theorem/coverage closure passes the
source checks independently, but the separate LaneDenotation31 reference-proof
closure has imported cohort discrepancies. Its structural/finite native evidence
remains recorded; coherent release native-source law is unconfirmed. See
FINAL-AUDIT-SCOPE.md. This does not remove a deployed V152–V154/native premise.
