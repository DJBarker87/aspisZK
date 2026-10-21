# Row-aware oracle-port draft, 2026-10-21

Branch `codex/cx-rowaware-draft-20261021`, base `b81ae0928`.
This is an unmerged draft based on the unapproved oracle-port draft. No
production or existing Lean module is modified.

## Causal refinement

`OraclePortRowAwareCausalD1` specifies a table-only causal gate. A witness
starts at a tag-2 initial message, recursively caches every query in each
preceding sampler row, and provides recognition of that row's first cell
in a subtable of the current table. An absorb cannot pass merely by being
parseable in isolation. The witness uses the actual 33-row sampler schedule,
including reseed and query rows. The gate is a noncomputable specification,
not an executable parser or a source refinement.

The decoder filters `RecordedBinaryExperimentBin.dec`, preserving its whole
background computation and output function whenever the gate passes.
`decode_some`, `retained_value`, and `density` prove this and retain the
existing classifier budget. These are retained-start results, not yet
accepted-run completion or equality of the complete extractor.

## Verification

Focused local compiles use the required 4.32.0 toolchain and
`-j1 -M4400 -DElab.async=false`, shared mkdir lock, and private objects.
Per-attempt source snapshots, exact commands, revision, hashes, dependency
fingerprint, exit, wall time, peak RSS, swaps and axiom output are in
`../evidence/rowaware-draft-20261021/manifest.json` and attempt directories.
The first two attempts failed on a missing namespace for `Table`; the
resulting elaboration diagnostics are not accepted proof evidence. Attempt
3 passes all four axiom audits with standard axioms and zero swaps.

## Outstanding investigation

Causality alone does not exclude the frozen node overlap. The final
collision-free counterexample below passes even the stronger full-row gate.
No Q+34 endpoint or premise removal is claimed.

## Fully cached causal witness

`OraclePortRowAwareWitnessD2`, `WalkD3`, `RecognizedD4`, and
`GateWitnessD5` (each with the `OraclePortRowAware` prefix) replace the
older four-cell support by the complete row-zero cache: initial answer
`03^32`, row-zero absorb answer `04^32`, squeeze answer `05^32`, and
advance answer `12 || 00^31`. All four answers differ and none is the IV.
The previous leaf answer `00^32` is omitted entirely. The resulting table
still recognises the same frozen 65-byte Merkle node as a row-one absorb.

The gate witness uses the actual literal sampler, not a detached label or
an assumed prefix-recognition predicate. `initial_eval` proves its entire
row-zero evaluation; `first_node` proves its next first cell is the node;
`gate_node` recursively supplies the cached predecessor and an initial
start recognised in the empty subtable. Thus even the stronger requirement
that the whole predecessor row (including its squeeze) was cached does not
exclude this node.

The first combined witness compile hit -M4400 (4,813,848,576-byte peak).
Its replacement splits the finite fibers, walks, and recognition across
modules and keeps table/walk definitions opaque. No cap was raised and the
failed combined source was not retried unchanged. Subsequent failed
elaborations involved missing canonicality proof arguments, the reserved
word `prefix`, or unwanted reduction of padded addresses. Explicit symbolic
rewrites and opaque address constants fix these; the final split modules
compile and all their axiom audits are standard. These remain focused draft
checks, not a unified release replay.

## Density, mass, and completion boundary

`OraclePortRowAwareTransportD7.classifier_density` retains exactly
`PerAttemptEnvelope.B`. `decoded_union_bound` retains `N * B` for an
explicit `DecoderReadsBound`; no query factor is removed. The binary
collision event is independent of the decoder, and
`binary_mass_unchanged` retains exactly `BinCombinedMerkleCollision.kappa Q`
(`6 * Q^2 / 256^32`) for the same experiment and first-read bound. This is
an unchanged probability **bound**, not an assertion that the filtered
classifier event has identical probability.

`completion_transport` preserves the complete recovered literal transcript,
message, and challenge of existing port completion at every retained row.
`completion_of_checks` composes the existing RWire-derived
`OraclePortCompletionDraft.completion_of_checks`. Both explicitly require
`GateAtRows D dO P Q`; this has NOT been discharged on all accepted
collision-free runs. In particular, pending-prefix answers are supported by
the old decoder, while this draft gate asks for a completely cached
predecessor row. One must not silently identify these domains. Equality of
the complete extractor output on all accepted collision-free runs remains
unproved; `retained_value` covers only individual retained starts.

`OraclePortRowAwareNoCollisionD6` adds the full five-reader check for the
five-cell trace, for every Q. Each answer differs from iv, every previous
answer, and every target parsed from the current or any previously cached
input. `safe_no_collision` proves this suffices without using a false
`Small T Q` side condition. `clean_safe` evaluates only five byte lists of
at most 75 bytes, five reader indices and 32-byte state equalities; it never
enumerates the oracle state space or padded address universe.

## Checked obstruction and stopping point

`OraclePortRowAwareObstructionD8.cached_table` identifies the support table
with the chronological application of exactly the four row-zero cells.
`frozen_node` identifies the fifth input with the frozen `12 || left32 ||
right32` encoding. `causal_node_without_collision` combines this table
identity, `Gate`, absence of the exact five-reader collision event for every
Q, and exactly **one** fresh recognised start on the fifth query.

`OraclePortRowAwareCounterclaimD9.causal_clean_zero_is_false` compiles the
negation of this exact subclaim (with the namespace abbreviations opened):

```lean
∀ (prior : List (Bytes × State)) (cs : BinMerkle32Path.Children),
  let a := OracleDecisionDomSepFrozen.node cs
  let T := applyTrace emptyTable prior
  Gate D a T →
  ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
    BinRawByteCollisionTargets.pred Q) emptyTable (prior ++ [(a,fun _ => 6)]) →
  decoderFirstReads (decode D) T [(a,fun _ => 6)] = 0
```

The counterexample uses the familiar overlap:

```
node:    12 || 00^32 || a1 || 00^31
absorb: (12 || 00^31) || 00 || a1 || 00^31
```

Its preceding row is fully recognised and cached at the correct row; no
collision is available to charge to κ. The problem is the **current**
row-one message: the model accepts a 31-byte payload while the frozen
row-one record has five bytes. Checking the predecessor's causal chain
cannot reject that current payload. This is a false subclaim, rather than
a resource or normalization obstruction. The one failed D8 attempt had the
frozen-byte equality oriented backwards; the repaired symbolic equality
passes without a cap change.

Scope matters: this five-query prefix is **not** a complete accepted frozen
57,607-byte proof, not a deployed minimal multiproof, and not a counterexample
to the aggregate Q+34 bound restricted to such runs. It disproves the
proposed general inference that a node extending a recognised prefix must
involve a collision. A separate accepted-source exclusion/charging proof
could still establish Q+34. This draft does not assert that accepted-source
exclusion is impossible.

The requested unconditional zero-node-start route stops here. Restoring
Q+34 still needs either a decoder that also checks frozen current-row
message grammar, with its same-run completion and extraction proof, or a
sharper aggregate charging proof. The prior source-frame length envelope
would exclude this node under the first approach, but source-frame
membership cannot be assumed for arbitrary candidate starts. It must be
proved at the required accepted-run boundary. No Q+34 endpoint is emitted;
the prior conservative endpoint is retained.

## Signature audit and final verification

`signature-audit.json` checks all 25 existing headline/final-soundness
modules against base `b81ae0928`, including `R1FinalSoundnessBinPerQueryR19`.
Every file is byte-identical and every signature diff is empty. No premise
is removed or advertised as removed. `GateAtRows` is a new, explicit
conditional transport obligation, not a strictly weaker replacement of an
existing endpoint premise.

Nine new modules pass, with 30 theorem axiom reports, all subsets of
`{propext, Classical.choice, Quot.sound}`. All 21 actual attempts are retained;
12 failed attempts have diagnostics and source snapshots, with no successful
claim based on them. Every attempt has zero swaps. The largest successful
peak is 4,309,843,968 bytes; the single cap failure and its split replacement
are recorded above. `audit.py` checks final source/receipt agreement, each
new theorem's axiom audit, import-object hashes, resource fields, forbidden
proof constructs, and the unchanged existing endpoints.

| Module suffix | Green attempt | Wall seconds | Peak RSS bytes |
|---|---:|---:|---:|
| CausalD1 | 3 | 5.247 | 3613851648 |
| WitnessD2 | 2 | 11.433 | 3623878656 |
| WalkD3 | 2 | 5.556 | 3535257600 |
| RecognizedD4 | 1 | 22.178 | 4309843968 |
| GateWitnessD5 | 6 | 10.371 | 3628810240 |
| NoCollisionD6 | 3 | 7.933 | 3678175232 |
| TransportD7 | 1 | 6.556 | 3623698432 |
| ObstructionD8 | 2 | 4.186 | 3627204608 |
| CounterclaimD9 | 1 | 8.853 | 3610279936 |

This is focused draft evidence. No frozen-manifest release replay, Rust/SBF
rebuild, Aeneas replay, or runtime test is warranted by these additive
mathematical modules. No existing Lean module, S1/S3/S4/S5/S9/S10 candidate,
M10 instrumentation, sibling worktree, wallet key, or shipped verifier is
modified. No object file or binary is committed. Each completed stage is
committed locally; nothing is pushed or merged.
