# Selected Wire/opening execution continuation

Date: 2026-09-11

Base revision: `531b50ed6cd06d5902417edf614daee137c19acb`

## Result

The selected q22 Wire/opening path now composes through the exact byte layout,
the Rust-shaped functional Merkle verifier, concrete packed-record decoder and
opened-value terminal.  The headline theorem is
`successful_complete_selected_wire_constructs_ideal_execution_or_auth_failure`.
Its proved endpoint is:

```text
successful selected Wire parse
+ successful Rust-shaped minimal-multiproof verification
+ separate causal C1/C2 prefix answer logs
+ canonical parsing of the same 22 packed records
+ checked inverse construction
+ the actual shifted opened-value terminal equality
  => RawLogTruncatedDigestCollision
     OR C1LateTargetHit
     OR C2LateTargetHit
     OR (SuccessfulAt AND the same ideal execution accepts)
```

The successful branch no longer assumes `OpeningEquality`.  It is constructed
from the two authenticated leaf projections and the same 621-byte record at
each original query ordinal.

This constructs `SuccessfulSelectedVerifierRun.SuccessfulAt`; it is no longer
only a predecessor of that result. The remaining lower deterministic seam is:

```text
compiled relation_callback/performance_verifier success
  => the already modelled total functional parser/Merkle execution
     AND identical transcript-derived challenges and path checks
```

Until that refinement is proved, `MinimalMultiproofPaths.Accepted` must not be
silently renamed Rust verifier success.  The three authentication alternatives
also remain symbolic here; their Fiat--Shamir/random-oracle resource bound is a
separate ledger obligation.

## New theorem chain

- `AuthenticatedPhaseWords.accepted_c2_opening_prefix_or_late_target_or_collision`
  supplies the post-lambda/chi C2 counterpart of the existing early-C1 binder.
- `SelectedMultiproofPrefixProjection.accepted_all_projections_or_shared_failure`
  constructs both paths from one typed selected merge execution and produces
  either all 22 paired projections or the shared explicit failure union.
- `PrefixPackedQueryBatch.raw_slots_of_paired_projection` turns a paired
  projection of the same canonical record into exact gamma-batched values for
  all four slots.
- `SelectedMultiproofOpeningEquality.accepted_opening_equality_or_authentication_failure`
  constructs `FixedWordQueryTerminal.OpeningEquality` for the complete q22
  schedule or returns the explicit authentication failure.
- `SelectedWireOpeningTerminal.accepted_terminal_or_authentication_failure`
  composes that result with the checked inverse and real local-value recurrence
  to obtain `CausalOrderedRelation.accepts`.
- `SelectedWireBytes` proves the exact 697-field/root/nonce/record/frontier
  projections from one accepted 40,282-byte-layout parser result.
- `RustShapedMinimalMultiproof.verify_selected_accepted` proves that the total
  pair/single loop, guards and terminal root checks construct typed `Accepted`.
- `SelectedWireMerkleRun.successful_constructs_accepted` binds that verifier to
  the same parsed Wire roots, records and frontier halves.
- `SelectedAuthenticatedSuccessfulRun.wire_success_or_authentication_failure`
  constructs `SuccessfulAt` and reuses the existing ideal-execution theorem.
- `SuccessfulCompleteSelectedWire.successful_complete_selected_wire_constructs_ideal_execution_or_auth_failure`
  is the final composition; it takes no independent `Accepted`, roots, records
  or frontiers.

`FixedWordQueryTerminal` was also repaired: the missing
`AspisV5FriRelationCandidateBridge` namespace was opened, and the residual
proof now uses a small congruence instead of a deep unfolded `change`.  Its
focused replay is green and has no `sorryAx`.

## Evidence

All green runs used Lean 4.32.0, `-j1 -M9500`, a dedicated user systemd scope,
`MemoryHigh=8G`, `MemoryMax=10G`, `MemorySwapMax=0`, and `CPUQuota=200%`.

| Target | Exit | Wall | Peak RSS | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `AuthenticatedPhaseWords` | 0 | 2.78 s | 6,702,780 KiB | 0 | standard only |
| `SelectedMultiproofPrefixProjection` | 0 | 2.85 s | 6,707,880 KiB | 0 | standard only |
| `PrefixPackedQueryBatch` | 0 | 2.91 s | 6,828,420 KiB | 0 | standard only |
| `FixedWordQueryTerminal` | 0 | 3.28 s | 6,847,580 KiB | 0 | standard only |
| `SelectedMultiproofOpeningEquality` | 0 | 2.96 s | 6,842,092 KiB | 0 | standard only |
| `SelectedWireOpeningTerminal` | 0 | 2.88 s | 6,839,580 KiB | 0 | standard only |
| `SelectedWireBytes` | 0 | 3.36 s | 6,715,892 KiB | 0 | standard only |
| `RustShapedMinimalMultiproof` | 0 | 3.26 s | 6,691,944 KiB | 0 | standard only |
| `SelectedWireMerkleRun` | 0 | 2.95 s | 6,850,536 KiB | 0 | standard only |
| `SelectedAuthenticatedSuccessfulRun` | 0 | 3.23 s | 6,891,964 KiB | 0 | standard only |
| `SuccessfulCompleteSelectedWire` | 0 | 2.86 s | 6,881,368 KiB | 0 | standard only |

The standard axiom set printed by these leaves is `propext`,
`Classical.choice`, and `Quot.sound`.  The immutable source/log/manifest
triplets are stored beside the experiment sources.  Failed focused attempts
were local interface debugging only and are not represented as evidence.

## Security and wire scope

No proof bytes, messages, rounds, queries, or verifier checks were added.  The
body census therefore remains 40,282 bytes.  No CU or prover-time measurement
was performed in this continuation.  This result supplies no grinding credit
and does not yet numerically charge the authentication alternatives.

## Decisive next experiment

Prove the compiled Rust/Aeneas refinement that successful
`verify_two_minimal_subtrees_v7_bytes` execution equals the now-green
`RustShapedMinimalMultiproof.verify`, including its mutable `Vec` swaps and
byte-frontier decoder. The theorem above already completes the composition
from that functional boundary to `SuccessfulAt`; after the refinement, the
only remaining authentication work is the explicit random-oracle/Fiat--Shamir
charge for its three named bad alternatives.
