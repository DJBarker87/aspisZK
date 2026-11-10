# Aspis ZK: a formally verified STARK verifier on Solana

Aspis is a private payment system for Solana. Its core is a zero-knowledge
verifier that runs natively on chain, with no trusted setup and no ceremony.

The mathematics is proved in Lean 4. The soundness of the protocol is proved
to 100 bits: an attacker cannot get a false spend accepted except with
probability below 2^-100 per hash query. The privacy theorem is proved too: a
proof reveals nothing about the spender's secrets beyond the public statement.

The Rust is then matched to that mathematics. The verifier's source is
translated into Lean automatically, and every function it uses is proved to
behave as the mathematics says. The same work is under way for the prover.

The proofs are Circle STARKs over the Mersenne-31 field, checked inside
ordinary Solana transactions.

[A plain-language introduction is at aspis.djbmaths.uk](https://aspis.djbmaths.uk/).

## Live on Solana

In November 2026 the pool and verifier ran together on Solana devnet as
deployed programs. The verifier is immutable. They settled a private transfer
and a private withdrawal, each in two transactions of about 1.2 million
compute units. The first transaction runs the opening stage of the proof and
writes a checkpoint; the second finishes verification and settles the payment.

- Private transfer:
  [stage 1](https://explorer.solana.com/tx/pUEwuhuSNmr8PK159eVxZhwJGHAceLr8qLLcE4b3gdJ3qTuFz9NgoGXwhe6VrL646VhRj6AzmSXuyuQTq8Hz4i8?cluster=devnet),
  [stage 2 and settlement](https://explorer.solana.com/tx/5bPwiKGmcXgRQnEJfbUrxHU1kuQgu3Q4GMrZ8V76jCHTxmqr3zVKkjcsk5JNmP9PXtimkrQBzvf5SQ4Chq4UBmCt?cluster=devnet)
- Private withdrawal:
  [stage 1](https://explorer.solana.com/tx/2QS4o2i1TpocPc4xeDh9KFBLuKaqBAbSTkiwiNbqecrNoTZvq1rjP8tVyu6BfBGuYFqJnpe4ueG3Ev5q7HvgjPpo?cluster=devnet),
  [stage 2 and settlement](https://explorer.solana.com/tx/54t54tQ14sNpUxU6cQJoi4e1Vpbb8bZhwMrDxmnrUk9fgEPBCmcZi3Qzwmc4F9SjmgoeTXfLDDZ7TfA8QBUjW8EM?cluster=devnet)

The run also submitted a replay of each settlement and a tampered proof for
each. All four were rejected, and no account changed.

Both programs rebuild bit for bit from the source in this repository:
[`37hdATMk…Db3Zt`](https://explorer.solana.com/address/37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt?cluster=devnet)
(pool) and
[`GqZzWuGT…nr5hy`](https://explorer.solana.com/address/GqZzWuGTojfsxYnDzmyWKhdPGkce19xN1Txu9Vgnr5hy?cluster=devnet)
(verifier). The full record of the run is in
[`docs/r1/DEVNET-RUN.md`](docs/r1/DEVNET-RUN.md).

## The proof

**Soundness, to 100 bits.** One theorem covers the whole spend path: both
transactions, the checkpoint between them and the call into the pool. It
considers an attacker who can behave in any way at all, adapt to everything it
sees, and query the hash function as often as it likes. An attacker making Q
hash queries gets a false spend accepted with probability about (Q+34)/2^105,
which is below (Q+1)/2^100 for any feasible Q. The figure takes no credit for
proof-of-work and places no restriction on the attacker.

**Privacy.** A second theorem says that what the prover publishes can be
reproduced by a simulator that never sees the spender's secrets, so a proof
leaks nothing beyond its public statement.

**Matching the Rust.** The verifier's Rust is translated into Lean
automatically. All 599 functions it uses, from the field arithmetic up to the
two entry points, are proved to return the same results, fail in the same
cases and make the same hash calls in the same order as the mathematical
model. The prover is going through the same process.

Lean accepts all of it with only its three standard axioms. For more detail,
see [the soundness theorem with a plain reading](docs/r1/TOP-THEOREM.md),
[the derivation of the bound](docs/r1/SOUNDNESS-STATUS.md) and
[the function-by-function ledger](docs/r1/LEDGER-599.md).

## What is next

Two things remain. For soundness, the last checks connect the proofs to the
exact deployed bytes; they are listed in
[`docs/r1/OPEN-GATES.md`](docs/r1/OPEN-GATES.md). For privacy, the prover's
Rust is being matched to the privacy theorem in the same way the verifier's
was matched to the soundness theorem.

## The repository

| Path | What is there |
| --- | --- |
| `crates/`, `programs/` | The frozen source: the verifier and the pool |
| `docs/r1/` | The proof package: security contract, theorems, ledger, devnet record, open items |
| `AspisFormal/`, `aeneas-verif/`, `kani-verif/` | Lean and Kani work for earlier versions |
| `docs/` | Design notes and earlier-version records ([index](docs/README.md)) |
| `release/`, `results/`, `paper/` | Earlier release bundles, measurements and papers |

Build instructions, including how to check a build against the deployed
programs, are in [`docs/r1/BUILD.md`](docs/r1/BUILD.md). The full Lean
development is on the
[`research`](https://github.com/DJBarker87/aspisZK/tree/research) branch.

## On mainnet

Aspis has already verified a private spend on Solana mainnet. In July 2026 an
earlier version of the verifier checked a 75 KB zero-knowledge proof, advanced
the pool and marked the nullifier spent, all in one finalized transaction of
1.33 million compute units:
[`EJviPgF…R3vJ2fE`](https://explorer.solana.com/tx/EJviPgF12i9iK2CveVaQSMeFQqDMFPQ1iPRUYEwNQE3zGquTUZNJXPZEENorcQtsnQj1orFmH1TPsgdbR3vJ2fE?cluster=mainnet-beta).
The record is in [`docs/v5-mainnet-demo.md`](docs/v5-mainnet-demo.md).

## About

I built Aspis as a solo research project with AI-assisted engineering.
Citation details are in [CITATION.cff](CITATION.cff). The code is licensed
under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE).
