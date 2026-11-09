# Aspis ZK: native Circle STARK verification on Solana

Aspis is a transparent, trusted-setup-free zero-knowledge payment system for
Solana. Its on-chain verifier uses Circle STARK techniques over the M31 field,
and the accompanying proof work is written in Lean 4 and connected to the
production Rust with Charon and Aeneas, which translate Rust functions into
Lean definitions that can be reasoned about directly. The current
implementation is R1, in which a private spend is verified across two Solana
transactions: the first runs stage 1 of the verifier and stores a checkpoint
account, and the second resumes from that checkpoint, completes verification
and settles the spend in the Pool.

[Read the plain-language introduction at aspis.djbmaths.uk](https://aspis.djbmaths.uk/).

## What has been proved

The R1 verifier, at the frozen source revision `4bb3b3f51e16`, reaches 599
distinct Rust functions across its two transactions, from field arithmetic and
the transcript up to the stage-1 and stage-2 entry points. For each of them
there is a verified statement in Lean: on every input in its stated domain, the
function, as translated from the frozen Rust by Charon and Aeneas, returns the
same result, fails in the same way and makes the same calls in the same order,
hash calls included, as the mathematical model the soundness argument reasons
about; and every caller proves, rather than assumes, that its uses of a callee
stay inside that callee's domain. All 599 statements are proved, with none left
qualified or open. For most of them the Lean side is the tool's own
translation of the frozen function; for the small number where the tools could
not produce a usable translation, the proof is against a transcription of the
frozen body that was reviewed by hand and is recorded, function by function, as
a trust row in the proof package, so that nothing of this kind is hidden inside
a theorem's hypotheses.
A table of all 599, with the Rust function and the Lean theorems behind each,
is in [`docs/r1/LEDGER-599.md`](docs/r1/LEDGER-599.md).

On 9 November 2026 these statements were composed into a soundness theorem for
the actual two-transaction spend path, `AspisR1.TAS_FinalB.deployed_splitB`,
and its averaged form `AspisR1.TAS_FinalB.deployed_charge`. They prove every
conjunct of the adopted statement of the security property,
`AspisR1.RPx_Deployed.deployed`, for the pair of transactions the adversary
actually submits, with one change approved by the owner: the conjunct about
the spend's outcome now holds unless the run falls in a hash-collision event,
and that event is already paid for inside the numeric bound below. The
assembly takes 22 interface arguments, and in the final theorem every one of
them is supplied by a proved term rather than left as an assumption, so what
remains in the statement is its own parameter (the adversary's query budget),
the description of the two-transaction run, and the named trust rows.
The adversary is arbitrary and fully adaptive; it may query the hash oracle as
it likes before choosing each transaction, and every query counts, repeats and
rejected attempts included. Lean's `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound` for both theorems, and an independent walk
of the proof terms, about 146,000 constants for each, reached exactly the same
three axioms; a scan of the whole closure of 20,019 modules found no dangling
reference, duplicated declaration or mismatched import.

Two of the pieces this needed are worth naming. The first is a correction to
the model of the host environment, made on 9 November: the old model left the
zero-filled buffer allocation at the start of stage 1 as a placeholder that
never returns, and Lean showed that under it the first transaction could never
be accepted, which would have made any theorem stated there vacuous for real
runs. The corrected model allocates as the frozen source does, under the
existing allocator trust row, and both theorems are stated at it. The second
is the pair of theorems that carry the model across to the program's own stage
code, `AspisR1.NOQ_FinalCombined.field` for the first transaction and
`AspisR1.NOF_A2FieldCorrected.field` for the second: whenever the first
stage's code returns successfully with a saved checkpoint, the model returns
the same checkpoint, and when the code rejects the model does not accept; the
second gives the same agreement for the second stage's successful runs.

The averaged theorem rests on two facts about one fixed recorder program, which
replays the adversary's run and records its hash reads. For every oracle, if
the two transactions are accepted and the spend's outcome property fails, the
recorder finds a collision among those reads; and the average of that collision
event over a random oracle is at most the bound below. The theorem states
these as two facts rather than as one averaged statement about the failure
itself, and a third conjunct bounds the model's failure probability by the
same quantity.

The bound is `F3T_Numeric.total`, in the contract's own units. For an
adversary making at most Q hash queries,

```text
total(Q) = (Q+34)·B + 6·(Q+1161)²/2^256 + 6·(Q+2965)²/2^256 + 2^-126 + 2^-454,
B = 15/2^109 ≈ 2^-105.093
```

where the first term charges each of the Q queries and the 34 starts of the
submitted transcript, the next two are collision terms, and the last two are
the extractor's abort allowance and the query-scan exhaustion term; there is no
proof-of-work or grinding credit, and no probability is divided by attack work.
With no adversary queries, total(0) ≈ 0.99609·2^-100 ≈ 2^-100.0056, and
`F3T_Numeric.margin_exact` proves that it lies below 2^-100 by about 2^-108.
`F3U_Range.per_attempt` proves total(Q) ≤ (Q+1)·2^-100 for every Q up to
7388980242446479800895501321004157112314840375 (about 2^152.372), and
`F3U_RangeMaximal.exact_range` proves that this range is exact. For every Q
below about 2^100 the bound is approximately (Q+34)·2^-105.093. The full
derivation is in section 3 of [`docs/r1/SOUNDNESS-STATUS.md`](docs/r1/SOUNDNESS-STATUS.md),
and both theorems are printed in full, with a reading of each binder, in
[`docs/r1/TOP-THEOREM.md`](docs/r1/TOP-THEOREM.md).

## What is not yet established

The release target, 100-bit classical soundness per attempt for the actual
frozen spend path with no proof-of-work credit, is not yet established, and
eight gates stand between the theorems above and that claim; each is described
with what would close it in [`docs/r1/OPEN-GATES.md`](docs/r1/OPEN-GATES.md).
Many of the Lean files the tools generated from the Rust cannot yet be traced
to a reproducible run of those tools, so they must be regenerated and proved
equal to the committed ones. The final proof closure has been checked against
cached builds but not yet rebuilt cold from source. The proofs are about the
Rust source, and the final audit tying that source to the deployed binary is
not done. The translations behind the proofs use checked arithmetic while the
deployed program wraps on overflow, and the transfer between the two is proved
only in part. The theorem takes the Pool's actions in the recorded run as
given, and the owner has yet to decide whether to bring the Pool inside the
security game or to state the claim as conditional on it. Repeated attempts
are covered within one experiment, but a bound for a campaign of separately
submitted spends is so far proved only for a stand-in model, with its
connection to the real host still open. No full witness yet shows that a real accepted transaction pair satisfies the
theorem's description of a run. And the trust inventory has still to be
matched one to one with the final closure, with a removal condition for every
row.

Three things are outside this claim altogether. Privacy is a separate
property with its own contract and its own theorems, and nothing here bears on
it. Settlement in the Pool is not covered, because the Pool's execution enters
only as an assumption about the recorded run. Liveness is not claimed: one
standard-library panic path has neither its reachability nor its exclusion
proved, though it can only abort a transaction, never make a false spend
accepted.

## Running on Solana

On 29 October 2026 the release R1 verifier was deployed to Solana devnet as a
new immutable program, `CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ`, whose
1,563,728-byte ELF, SHA-256 `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`,
was rebuilt bit for bit from the frozen source. It settled a private transfer,
in transaction [`53pTHDf…m2hhvR`](https://explorer.solana.com/tx/53pTHDfJBmqX7hdxPofSfajURpMhCiB6ceAdMw9ftf3RAXZ6k8D26WaW4MGito2Ty3kRQrAXQSDJ5QBNFsm2hhvR?cluster=devnet)
(stage 1, 1,214,746 compute units) followed by [`FNLSBxj…PCFxF`](https://explorer.solana.com/tx/FNLSBxjiJ8jPYzE2E25BCgzJ6rm9yrSXnRMgwhj3E5yxwU4wYPfs9vugucr6cVrgnhem2b6TbqPCe3PKjPRFCxF?cluster=devnet)
(stage 2 and settlement, 1,145,305), and a withdrawal, in
[`3C6fKwt…5ut4F7L`](https://explorer.solana.com/tx/3C6fKwts7pAaTko8kJvBJk4weuUc9y7dfbLTGjRiKuqXo6fWr7xvNoG7w19Nb8V9yY6erAda5jt65khHY5ut4F7L?cluster=devnet)
(1,206,747) and [`46bYP2B…cES3wn2`](https://explorer.solana.com/tx/46bYP2Bz1sTiwNDSFxYVumN1kPYa4TARupv8ptAMMx7ixwSNCZwU59WLNDz1zv5V97qgKFp6NtY4njs9rcES3wn2?cluster=devnet)
(1,154,975), which moved 250 test tokens out of the vault. A replay of each
settlement was rejected because its nullifier had already been consumed, and a
mutated stage-1 proof was rejected for each, with the protected accounts and
the fresh checkpoint left unchanged. The proofs used public test fixtures, so
the run demonstrates execution on a public cluster, not privacy, and the Pool
build that ran there predates the removal of the legacy Pool instructions on
9 November; the full record, with every signature and account, is in
[`docs/r1/DEVNET-RUN.md`](docs/r1/DEVNET-RUN.md). R1 has not been deployed to
mainnet.

The earlier V5 verifier has already completed a finalized mainnet
transaction. On 24 July 2026 UTC it verified a 75,358-byte private-spend proof
on Solana mainnet-beta, advanced the pool and recorded the nullifier as spent
in one transaction using 1,334,452 compute units:
[`EJviPgF…R3vJ2fE`](https://explorer.solana.com/tx/EJviPgF12i9iK2CveVaQSMeFQqDMFPQ1iPRUYEwNQE3zGquTUZNJXPZEENorcQtsnQj1orFmH1TPsgdbR3vJ2fE?cluster=mainnet-beta).
Its evidence is kept in [`docs/v5-mainnet-demo.md`](docs/v5-mainnet-demo.md)
and [`release/`](release/). V7, the one-transaction design that preceded R1,
is kept under [`docs/v7/`](docs/v7/) as the previous design.

## Repository map

| Path | Contents |
| --- | --- |
| `crates/`, `programs/` | The frozen R1 source: verifier in `programs/r1-cost-probe` and `crates/aspis-r1-cost-probe`, Pool in `programs/aspis-pool` |
| `docs/r1/` | The R1 proof package: status, contract, theorems, ledger, trust inventory, devnet run, build, open gates |
| `docs/research/v8-r0-zk-20261009/` | Workspace path dependencies of the frozen manifests (extracted writer copies and the prover-side checker) |
| `AspisFormal/`, `aeneas-verif/` | Lean proofs and Rust-to-Lean bridges for V5 and V7; the R1 Lean development is on the `research` branch |
| `kani-verif/` | Kani proof bundles for V5 helpers |
| `release/`, `results/` | Frozen V5 release inputs, the finalized mainnet bundles, and runtime measurements |
| `docs/` | Design notes, the V5 and V7 records and dated research notes ([index](docs/README.md)) |
| `paper/` | Formalization report and construction paper (V5 era) |
| `xtask/`, `scripts/`, `tools/`, `config/`, `manifests/`, `audit/`, `archive/` | Build, deployment and evidence tooling, probes, and archived source manifests |

## Reproduction

The devnet ELF is built from the repository root with `cargo-build-sbf` from
Solana release 3.1.13; the exact command, environment, features and expected
hashes are in [`docs/r1/BUILD.md`](docs/r1/BUILD.md), together with the receipt
of the build that reproduced it bit for bit. The proof package in
[`docs/r1/`](docs/r1/) can be read on its own, and its README shows how to
check its copies against the research branch. The complete evidence, about
45 GB of Lean sources, compiled objects, receipts and logs, is on the
[`research`](https://github.com/DJBarker87/aspisZK/tree/research) branch at
the pinned commit `07123926e88273271344977a3fdc26d1780cde14`; it is not on
`main`. The V5 release bundles keep their own offline checks, described in
[`docs/README.md`](docs/README.md).

## Project

Dominic Barker built Aspis as a solo research project with AI-assisted
engineering. Citation metadata is in [CITATION.cff](CITATION.cff).

Licensed under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE).
