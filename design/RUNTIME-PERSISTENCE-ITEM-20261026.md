# Runtime persistence proposal — 26 October 2026

Target not yet established. **No trust item adopted. Actual deployed ledger delta: 0.**
This is the owner's requested route (2) decision packet. Proof modules have prefix
`CPR_`; receipts are under `evidence/cp-runtime-20261026/`.

## Exact proposed law

`lean/CPR_DataPersistence.lean`, `AspisR1.CPR_DataPersistence.TwoTransactionLaw`:

```lean
∀ t u, next t u → ∀ key, ordinary t key →
  loaded u key = visible (if success t then tentative t key else before t key)
```

`Image` contains only account-data bytes and the lamport count used to test
absence. `visible` maps zero lamports to absence and otherwise returns **data
bytes only**. The law asserts no next-owner, next-balance, account-record,
privilege, SDK-token, verifier-acceptance, checkpoint or source-trace equality.
`key` is a physical account key shared by the two observations. `next` means the
next transaction loading that account on the same bank lineage without another
account transaction in between. `ordinary` excludes fee payer / durable nonce
rollback special cases. `success` is final parent status after runtime checks,
not CPI success. `tentative` is the complete parent-final data/balance projection;
`before` is the pre-parent projection. Cleanup is at a transaction boundary only.

The earlier `CPR_Persistence.TwoTransactionLaw` full-image formulation is retained
as a checked sufficient alternative, not the proposed minimum.
`CPR_DataPersistence.of_full` proves the implication.
`CPR_DataGap.narrow_holds/full_fails` proves strictness: a changed positive
balance with identical bytes satisfies the narrow observation law but violates
full-image equality. Neither formulation is adopted as trust.

## Why existing items do not imply it

`RuntimeEntrypointAdmission` gives per-entry heap validity, empty tracked guards,
zero counters/external borrows, live owners, key/cell alias consistency and
`Library.related`. `RuntimeSyscall` constrains only returning digest values.
`Allocator` contains `allocate` and `cleanup`. D188/DigestExtraction equates owned
source functions and the digest wrapper. None mentions two transactions, a bank,
parent status, committed account storage, physical lifetimes or the next load.
`CheckpointVersionBinding` **already contains** the three requested history
fields; using it to derive its deployment instance would assume the conclusion.
S2X_RuntimeRetention explicitly distinguishes opaque P2/P3/P4 from an operational
interpretation. C3-BIN 01:20 adopts SDK borrow semantics only; the later 02:40
rollback description did not amend any of these exact Lean record types.

`CPR_Separation.independent` is a checked conservative-extension countermodel:
any inhabited old proposition `P` is retained unchanged with both a law-abiding
and a law-breaking loader. The latter discards a positive account on a successful
parent. `history_does_not_supply_loader` retains an actual supplied history
instance while the unrelated loader violates the law. This is an interface
separation, **not** a counterexample to deployed Agave or to a jointly inhabited
full cryptographic accepted-pair execution.

## Source behavior reflected

The Solana [transaction pipeline](https://solana.com/docs/core/transactions/transaction-pipeline)
describes the batch cache making earlier account changes visible to subsequent
transactions and distinguishes successful account commits from rollback-account
updates after failure (sections 6 and 8). The fee payer and advanced durable nonce
are exceptions; a claim that failure restores every byte of every account would
be false. This proposal excludes those exceptions for the protected account.

The retained read-only [Agave v3.1.13 loader](https://github.com/anza-xyz/agave/blob/v3.1.13/svm/src/account_loader.rs#L236-L324)
implements cached loading, zero-lamport absence, successful writable-account cache
updates and failed-transaction rollback-account updates. Source and tag hashes
were already pinned by `CPP_RUNTIME_REFERENCES.json` and
`CPP_RUNTIME_REFERENCE_REVISION.json`; these are reference behavior, **not a pin
of the deployed validator or feature set**. An owner-approved interpretation must
also cover accounts-db fallback / bank lineage and physical key mapping.

## Conditional composition and limits

`CPR_DataTop.deployed` composes the ACTUAL `T2R_Top.deployed` and
returns `CPP_ProtectedResult.Outcome` on the SAME `f,s,run,tx2` witnesses.
It preserves the driver/dictionary equalities and headline Claims/bounds exactly.
`CPR_DataWriter.on_cuts` derives the committed-byte history from the SAME accepted
native TX1, CPP source-bank actions, the proposed law and actual TX2 entry view.
`CPR_AtomicBank.protection` proves no intervening writes for owner-checked source
actions, credits and cleanup; failed parents discard their tentative events.
The old history arrows in acceptance/caller are applied internally, with P2Prime
and FirstEntry unchanged. No history premise is supplied to the conditional top.

This is a conditional theorem for a **correlated, positive-balance writer whose
successful parent is adjacent to the reader transaction**. Added explicit source
representation obligations are `keyLaw`, `entry1`, `tentativeView`, `entry2View`,
parent `status`, adjacency/ordinary-key eligibility and writer input positivity.
They are NOT newly adopted trust items, and NOT silently proved by the two-TX
law. In particular `tentativeView` requires the complete source suffix of the
actual parent, not just a successful CPI copy; `entry2View` maps the physical
loaded image to the original e2 buffer. Arbitrary independent root entries and
zero-funded temporary accounts require more work. Claiming that the single law
alone universally removes the four rows on the original root would be false.
The law addresses bank persistence; it cannot manufacture physical/source
association. This limitation is part of the proposal submitted to the owner.

Conditional-row accounting: L094/L095 are constructed by native copy + computed
history + law/load interpretation; L096 is derived from source protection;
L180 is conditional on the stated correlated physical pair. **Actual deployed
L094-L096/L180 remain OPEN; actual recount delta is zero.** No whole-execution
equality, source-query allowance, crypto assumption or new trust record is added.


## Source-event association is a separate gate

Final account-image equality alone does not prove equality of ordered physical
account events. The preferred `CPR_PhysicalTop.deployed` additionally takes an
explicit local source-refinement obligation `eventsView`, and returns a history
whose `version.events` equals that supplied physical event projection on the SAME
source witnesses (`CPR_PhysicalResult.Outcome`). Its TX1 entry interpretation uses
`CPP_BankState.layout initial layout1`, so input lamports are also the same bank
projection. `eventsView` is NOT adopted trust; it remains to be proved from the
actual executor/source trace. A callback named `physicalEvents` is not itself a
certificate of a deployed recorder. The ordinary-key predicate, physical key
mapping, final parent status, full source suffix and reader-buffer projection
also need concrete instances.

Thus the requested **universal removal with the single law alone** is not a
valid claim on today's independently quantified root. `CPR_KeyGap.runtime_law`
satisfies even the stronger law, while `no_cross_key_history` rules out the
history between independently chosen unequal checkpoint images. This isolates
pairing, not full accepted verifier executions. `CPR_AdmissionGap.gap` separately
inhabits the complete SDK mathematical model and BOTH actual runtime admission
records with same key metadata and equal CP lengths but unequal buffers; it does
not claim native acceptance. `CPR_DataGap.old_items_do_not_supply_data_loader`
is the checked separation for the exact proposed byte-only loader law.

Do not turn any of these source-refinement obligations into runtime trust. The
owner can consider the narrow law against an explicit validator/feature pin;
the positive correlated branch's conditional composition is checked. Arbitrary
physical lifetimes, zero-funded temporary CPs, cleanup/recreation, failed writer
parents, source-event extraction and deployment adoption remain unclosed.

## Checked endpoint-history counterexample

`CPR_EventsGap.final_image_equal` proves that writing `[]` to key 0 and then
writing its original bytes back leaves the entire final byte ledger unchanged.
`runtime_law` satisfies the narrow two-transaction law with ordinary eligibility
and adjacency both true. `no_actual_history` proves there is no protected history
with THAT key and THAT event list. This is an account-event algebra countermodel,
not a claim that the verifier allows such writes. It shows why replacing
`eventsView` by endpoint byte equality is unsound. The **requested law-only
L180 closure has not been established**; no countermodel to all cryptographic
accepted-root hypotheses is claimed either.

## Validation and non-vacuity

`CPR_Nonvacuity.canonical_law` supplies a model of the operational law.
`nonempty_suffix` includes credit, an authorized foreign write and real cleanup
of another zero-funded key. `parent_failure` discards tentative writes and
credits. These establish local model non-vacuity, not a joint native/crypto/bank
inhabitant. `CPR_PhysicalOrder.original` maps the conditional strengthened result
back to the original FullResult on identical source witnesses and carriers.

Before/after source statements and the zero recount are retained in
`CPR_BEFORE_*`, `CPR_AFTER_*` and `CPR_LEDGER_DELTA.json` under the receipts
folder. `CPR_L024/stdout.log` prints elaborated root/result/continuation statements
and all then-current top-theorem axioms; the final independent event
counterexample has its own `CPR_L025` axioms audit. Only standard axioms appear
in successful receipts. See `CPR_HANDOFF.md` for exact resource totals, failures,
remaining obligations, inherited artifact pins and the unused budget.
