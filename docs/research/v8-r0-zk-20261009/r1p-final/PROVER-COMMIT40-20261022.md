# Prover commitment continuation 40

**Target not yet established.** The deployed statement image is D146; the
mask nonce is public and adversary-chosen, including after earlier oracle
queries. D143 observables are public statement bytes, submitted proof bytes
and answers to the adversary's own oracle queries. Timing and other side
channels are outside the privacy contract. Trust list: P1, P7, TrustedStd,
E1 (successful OS draws uniform and independent), E2 (atomic durable ledger).
No OS/fs failure probability or ledger-size restriction is introduced.

## Stage 1: private raw-seed memo counting

`ProverCommitPrivateMemo40` counts private raw seed suffixes for arbitrary
public prefixes. Both raw derivation inputs for field entropy and all raw
leaf-seed derivation inputs end in exactly their private 32-byte seed.
A query nominates at most one seed. `context_mass` permits arbitrary earlier
context, including adversary nonce selection after queries, followed by the
fresh E1 coordinate. `attempts_mass` combines individually established laws
without independence among events. These are counting lemmas, not a proof
that the complete adaptive runtime satisfies the required laws.

Each raw seed contributes Q*attempts/2^256. At Q≤2^64 and attempts≤128
(16 candidates times eight proof attempts), this is ≤2^-185. Two raw seeds
and two worlds give the explicit addition `4 * budget q attempts`.
No conditioning on nonzero selection is used. No reservation query is charged.

J9172 was a rejected parsing draft (`prefix` is reserved); J9173 compiles the
nine final theorems, exit 0, wall 2.26 s, peak RSS 4,076,840 KiB, zero swaps.
Every printed axiom is in [propext, Classical.choice, Quot.sound]. Full source,
dependency fingerprints and receipts are under
`evidence/prover-commit40-20261022/lean/`. Source revision is the base revision
plus retained exact overlays, not an attribution to a different checkout.

## Numerical before/after

Before (the active endpoint's arithmetic lemma):

```lean
theorem total_lt_target {q r : Nat} (hq : q ≤ 2^65) (hr : r ≤ 2^64) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget q + 2 * ProverCommitSeedEvent19.budget r +
      2 * charge < 1 / (2 : ℚ)^100
```

After (new conditional numerical envelope, not yet installed at the endpoint):

```lean
theorem total_lt_target {scan q attempts : Nat}
    (hs : scan ≤ 2^65) (hq : q ≤ 2^64) (ha : attempts ≤ 128) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget scan + 2 * ProverCommitSeedEvent19.budget q +
      2 * ProverCommitFuelMass22.charge + 4 * budget q attempts <
        1 / (2 : ℚ)^100
```

The existing seedGuess charge is retained separately. The prior part-39
conditional nonce memo term is superseded for this route by exact public-query
preservation; no uniform-nonce assumption is retained. Native execution and
FS experiment conversion remain to be connected before a deployed headline
can use this arithmetic.
