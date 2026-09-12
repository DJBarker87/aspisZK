# Authenticated opening / relation interleaving

Status: the previously misordered functional path is repaired and focused
Lean-checked.  Whole-verifier composition and literal Rust refinement remain
open.

## What changed

The earlier combined model ran the later relation responses before its Merkle
opening script.  The pinned verifier instead derives q22 and rho, authenticates
and decodes the openings, computes the shifted query increment, absorbs that
increment, and only then processes response1--response3 and alpha1--alpha3.

`FSInterleavedSelectedIncrementBoundary.lean` now implements that exact order:

1. `selected22` authenticates the 22 records against both chronological root
   cuts, threading every leaf/node call through the shared oracle;
2. a pure, hash-view-free stage parses the same body, decodes those records,
   checks all required chord inverses, folds the opened values, and constructs
   the canonical shifted increment;
3. the increment is absorbed under literal Rust label `PROFILE = 1` from the
   unchanged post-rho transcript digest; and
4. the three body-derived response records precede their three live alpha
   draws.

The same `positions` value is used for authentication and opened arithmetic.
There is no independent/stale query schedule.  The static allowance is
`1038 = 836 + 202`; padding does not issue dummy oracle calls.

`interleaved_success_decomposes` retains failed opened preparation as a named
branch.  More importantly,
`interleaved_ok_constructs_selected_and_increment` proves that an accepting
suffix constructs the exact authenticated trace, computed increment bytes,
and the actual later response/challenge run yielding the returned alpha values
and final digest.  None is supplied as a theorem premise.

## Focused replay

Base revision: `94cad3ee` (the file began before that commit and was replayed
after it).  Lean 4.32.0 ran on the Tailscale NUC under `MemoryHigh=8G`,
`MemoryMax=9G`, `MemorySwapMax=0`, and `RuntimeMaxSec=600`.

- Exit: 0
- Wall: 3.27 seconds
- Peak RSS: 6,766,040 KiB
- Swap: 0
- Source SHA-256:
  `6d8aeb6cf84a2aee8565ff830faaf3c80368cc0b147494842709289d18731dc0`
- OLean SHA-256:
  `473a367492ffa98b0510741a18bc27ea063cb9b5dbdf048ea2ea66061a170085`
- Axioms: `propext`, `Classical.choice`, `Quot.sound`

The private combined OLean directory reused pinned dependencies and is not a
first-party dependency rebuild.

## Remaining interfaces

- `cuts`, the selected positions, checked OOD `Data`, alpha0, rho, and the
  post-rho digest must still be constructed by one preceding live run.
- The returned opening values must be connected to the algebraic terminal
  relation and final acceptance, not merely serialized into the increment.
- The selected functional Merkle recursion and arithmetic still require
  literal effectful Rust refinement.
- This deterministic order theorem supplies no random-oracle probability,
  authentication collision bound, extraction result, or global soundness.

The proof body and verifier acceptance rules are unchanged.
