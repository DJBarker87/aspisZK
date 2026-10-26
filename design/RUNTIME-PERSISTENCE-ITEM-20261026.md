# Runtime persistence proposal — 26 October 2026

Target not yet established. **No trust item adopted. Actual deployed ledger delta: 0.**
This is the owner's requested route (2) decision packet. Proof modules have prefix
`CPR_`; receipts are under `evidence/cp-runtime-20261026/`.

## Exact proposed law

`lean/CPR_Persistence.lean`, `AspisR1.CPR_Persistence.TwoTransactionLaw`:

```lean
∀ t u, next t u → ∀ key, ordinary t key →
  loaded u key = visible (if success t then tentative t key else before t key)
```

`Image` contains only the account's owner, data and lamports, not instruction
privileges, temporary addresses, SDK borrow guards, verifier acceptance or
checkpoint equalities. `visible` maps a zero-lamport image to absence and a
positive-lamport image to that same image. `key` is one physical account key,
shared across the two observations. `next` means the next transaction loading
that account on the same bank lineage, with no intervening account transaction.
`ordinary` excludes fee payer / durable nonce rollback exceptions. `success`
is final **parent transaction** status after runtime postchecks, not CPI status.
`tentative` is the complete parent-final account image; it is not the image at
an internal source copy. `before` is the runtime image before that transaction.
The proposed law is about consecutive transaction observations only. It does
not identify an independently chosen Lean entry with a physical load.

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

`CPR_ConditionalTop.deployed` composes the ACTUAL `T2R_Top.deployed` and
returns `CPP_ProtectedResult.Outcome` on the SAME `f,s,run,tx2` witnesses.
It preserves the driver/dictionary equalities and headline Claims/bounds exactly.
`CPR_WriterLoad.on_cuts` derives the committed-byte history from the SAME accepted
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
