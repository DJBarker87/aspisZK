# Prover commitment part 22

Base `d9865ba52`; branch `codex/cx-prover-commit22-20261021`.

Work in progress. No deployed closure is claimed.

## Scope

D131 authorizes a fixed model fuel and an explicit exhaustion charge.
The shipped `Coins::nonzero` tests a 32-byte hash answer against all zero,
not an M31 field element. Its uniform-answer zero mass is 2^-256; the
requested M31 reciprocal is a conservative upper bound, subject to fresh
oracle addresses and the ROM transport. Three calls per attempt, eight
attempts give at most 24 instances. Model fuel will be five draws.

## Stage 1

Pending.

## Stage 2

Pending.

## Stage 3

Pending.

## Endpoint audit

Pending; RustProverRefinement remains explicit.
