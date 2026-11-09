# Aspis ZK: a trustless, formally verified Circle STARK verifier on Solana

Aspis is a private payment system for Solana, and at the heart of it is a
zero-knowledge verifier that runs natively on chain, needs no trusted setup and
no ceremony, and whose soundness is not argued in a paper but proved, as
mathematics, in Lean 4, against the Rust that actually runs. The proofs are Circle STARKs over the Mersenne-31
field; the verifier checks them inside a Solana transaction; and the theorem
that says a forged proof cannot get through is a theorem about that verifier's
own source code, translated into Lean by Charon and Aeneas, not about a model
someone drew of it afterwards.

[There is a plain-language introduction at aspis.djbmaths.uk](https://aspis.djbmaths.uk/).

## What we have built

**A verifier running on a public chain.** The latest Aspis verifier is live on
Solana devnet as an immutable program. On 29 October 2026 it verified a private
transfer and then a private withdrawal, each spread over two transactions: the
first runs the opening stage of the proof and writes a checkpoint, the second
picks the checkpoint up, finishes the verification and settles the payment in
the pool, at a little under 1.2 million compute units a transaction. It then
rejected a replay of each settlement, because the nullifier had already been
spent, and a tampered proof for each, with no protected account changing. The
signatures are below.

**Soundness proved, in Lean, end to end.** On 9 November 2026 the soundness of
the whole two-transaction spend path was assembled into a single theorem,
`AspisR1.TAS_FinalB.deployed_splitB`, with its averaged form
`AspisR1.TAS_FinalB.deployed_charge`. It says that an adversary who is
completely arbitrary and fully adaptive, free to query the hash oracle as it
likes before choosing each transaction, with every query counted, cannot get a
false spend accepted except with the probability below; and it says it about
the real spend path, the real checkpoint and the real pool call, with every
piece of the argument supplied by a proof rather than left as an assumption.
Lean reports only its three standard axioms for both theorems; an independent
walk of the proof terms, some 146,000 constants apiece, finds exactly the same
three; and a scan of the full closure of 20,019 modules finds no dangling
reference, duplicated declaration or mismatched import anywhere.

**The Rust shown to match the model, function by function.** The theorem is
only worth having if the verifier that runs is the verifier that was reasoned
about, and that correspondence has been established function by function. At the frozen source
revision `4bb3b3f51e16` the verifier reaches 599 distinct Rust functions between
the field arithmetic and the two entry points, and every one of them now has a
proved statement in Lean: on every input in its stated domain the function, as
translated from the Rust, returns the same result, fails in the same way and
makes the same hash calls in the same order as the model, and every caller
proves, rather than assumes, that it stays inside the domain of what it calls.
All 599 are proved, none qualified, none open; the full table is in
[`docs/r1/LEDGER-599.md`](docs/r1/LEDGER-599.md). For a handful of functions
whose translation the tools could not produce, the proof is against a
transcription of the Rust checked by hand, and each of those is named in the
proof package rather than hidden. The proofs also caught a model of the
host environment under which the first transaction could never have been
accepted; the theorems are stated at the corrected model, which allocates
exactly as the source does.

**The number.** For an adversary making at most Q hash queries, the probability
that a false spend is accepted is at most

```text
total(Q) = (Q+34)·B + 6·(Q+1161)²/2^256 + 6·(Q+2965)²/2^256 + 2^-126 + 2^-454,
B = 15/2^109 ≈ 2^-105.093
```

which is just under 2^-100 at Q = 0, stays below (Q+1)·2^-100 for every Q up to
about 2^152, and for any budget an attacker could actually spend is in effect
(Q+34)·2^-105. There is no proof-of-work credit in that figure, no restriction
on the attacker and no division of a probability by attack work. The derivation is in section 3 of
[`docs/r1/SOUNDNESS-STATUS.md`](docs/r1/SOUNDNESS-STATUS.md), and both
theorems are printed in full, with a plain reading of every part of each statement, in
[`docs/r1/TOP-THEOREM.md`](docs/r1/TOP-THEOREM.md).

## What is left

There is still some way to go before I describe this version as 100-bit
secure, and I will not do so until the remaining checks are complete. The
mathematics is in place; what remains is to tie the proofs to the deployed
bytes with the same rigour. The Lean that the tools generated from the
Rust is being regenerated and proved equal to the committed copies; the whole
proof closure is being rebuilt cold rather than checked against cached builds;
the translations use checked arithmetic where the deployed program wraps on
overflow, and that bridge is proved in part; and the pool's actions in the
recorded run are taken as given rather than brought inside the game. Each item,
with what closes it, is in [`docs/r1/OPEN-GATES.md`](docs/r1/OPEN-GATES.md).
Privacy has its own contract and its own theorems and is a separate story.

## On Solana

The verifier on devnet is program `CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ`;
its 1,563,728-byte ELF, SHA-256 `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`,
was rebuilt bit for bit from the frozen source, and it has no upgrade authority.
The private transfer is
[`53pTHDf…m2hhvR`](https://explorer.solana.com/tx/53pTHDfJBmqX7hdxPofSfajURpMhCiB6ceAdMw9ftf3RAXZ6k8D26WaW4MGito2Ty3kRQrAXQSDJ5QBNFsm2hhvR?cluster=devnet)
(stage 1, 1,214,746 compute units) followed by
[`FNLSBxj…PCFxF`](https://explorer.solana.com/tx/FNLSBxjiJ8jPYzE2E25BCgzJ6rm9yrSXnRMgwhj3E5yxwU4wYPfs9vugucr6cVrgnhem2b6TbqPCe3PKjPRFCxF?cluster=devnet)
(stage 2 and settlement, 1,145,305); the withdrawal, which moved 250 test tokens
out of the vault, is
[`3C6fKwt…5ut4F7L`](https://explorer.solana.com/tx/3C6fKwts7pAaTko8kJvBJk4weuUc9y7dfbLTGjRiKuqXo6fWr7xvNoG7w19Nb8V9yY6erAda5jt65khHY5ut4F7L?cluster=devnet)
(1,206,747) and
[`46bYP2B…cES3wn2`](https://explorer.solana.com/tx/46bYP2Bz1sTiwNDSFxYVumN1kPYa4TARupv8ptAMMx7ixwSNCZwU59WLNDz1zv5V97qgKFp6NtY4njs9rcES3wn2?cluster=devnet)
(1,154,975). The proofs used public test fixtures, so this is the verifier
working on a public cluster rather than a private payment of mine; the full
record, with every signature and account, is in
[`docs/r1/DEVNET-RUN.md`](docs/r1/DEVNET-RUN.md).

And Aspis has already been to mainnet. On 24 July 2026 the earlier V5 verifier
checked a 75,358-byte private-spend proof on Solana mainnet-beta, advanced the
pool and marked the nullifier spent, all in one finalized transaction of
1,334,452 compute units:
[`EJviPgF…R3vJ2fE`](https://explorer.solana.com/tx/EJviPgF12i9iK2CveVaQSMeFQqDMFPQ1iPRUYEwNQE3zGquTUZNJXPZEENorcQtsnQj1orFmH1TPsgdbR3vJ2fE?cluster=mainnet-beta).
Its record is under [`docs/v5-mainnet-demo.md`](docs/v5-mainnet-demo.md) and
[`release/`](release/); V7, the one-transaction design that came between V5
and the current version, is kept under [`docs/v7/`](docs/v7/).

## The repository

| Path | What is there |
| --- | --- |
| `crates/`, `programs/` | The frozen source of the current version: the verifier in `programs/r1-cost-probe` and `crates/aspis-r1-cost-probe`, the pool in `programs/aspis-pool` |
| `docs/r1/` | The proof package for the current version: the security contract, the status document, the two theorems in full, the 599-row ledger, the trust inventory, the devnet record, the open items |
| `AspisFormal/`, `aeneas-verif/`, `kani-verif/` | The Lean and Kani work for V5 and V7; the Lean development for the current version lives on the `research` branch |
| `docs/` | Design notes and the V5 and V7 records ([index](docs/README.md)) |
| `release/`, `results/` | The V5 release bundles, the mainnet transaction, and runtime measurements |
| `paper/` | The formalization report and construction paper from the V5 era |

How to build the ELF and check it against its hash is in
[`docs/r1/BUILD.md`](docs/r1/BUILD.md). The complete evidence behind the
proofs, some 45 GB of Lean sources, compiled objects and receipts, is on the
[`research`](https://github.com/DJBarker87/aspisZK/tree/research) branch at
commit `07123926e88`; it is not on `main`.

## About

I built Aspis as a solo research project with AI-assisted engineering. Citation details are in [CITATION.cff](CITATION.cff),
and the code is licensed under [MIT](LICENSE-MIT) or
[Apache-2.0](LICENSE-APACHE).
