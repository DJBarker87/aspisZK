# Merkle and transcript domain separation, 2026-10-21

Branch `codex/cx-domsep-20261021`, base `0559b538f`.
Additive prerequisites only; no endpoint port is authorised or performed.

## Finding

The frozen selected R1 Merkle grammar is separated from **public
initialisation**, and its Lean node encoding is faithful at the byte-list
level. That does **not** imply zero recognised decoder starts. The existing
compiled counterexample is a semantic row-one absorb, not an initialisation
frame. Its literal node encoding is already the frozen one. Consequently
this investigation cannot conclude Q+34; the established Q+1080 conservative
bound remains applicable. No premise removal is claimed.

## Frozen source inventory

`evidence/domsep-20261021/source-pins.json` pins 15 inspected source files at
research `b2727acd3` and this worktree. All 15 are byte-identical at inspection.
`inspect.py` regenerates the source inventory and checks the literal overlap.
This is source inspection, not an extracted Rust refinement proof.

The selected call chain is `verifier::candidate::batch_merkle_values` →
`batch_leaf` / `multiproof::verify_in_place`. The program's `Digest32`
backend calls Solana `hashv`, which hashes concatenated slices. The crate's
historical “cost probe” name does not make `aspis_core::merkle::node_hash`
the selected binary parent function.

| Input | Exact concatenation | Bytes |
|---|---|---:|
| C1 private leaf | `10 71 || packed480 || salt32` | 514 |
| C2 private leaf | `10 f1 || packed128 || salt32` | 162 |
| Folded private leaf | `10 72 || packed128 || salt32` | 162 |
| Selected binary parent | `12 || left32 || right32` | 65 |
| Semantic public init | `ASCII("UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3") || 00 || LE32(public.length) || public || c1_root32` | 75 + public.length |
| Opening transcript reseed | `ASCII("UNPROVED:R1:PRIVATE-SALTED:P3") || variant.tag || semantic_state32` | 62 |

Hexadecimal tags above are bytes. No parent depth, tree tag, length word or
salt is appended to a parent. All 18 levels, for C1, C2 and the padded folded
tree, use the same parent grammar. The folded index is u/4; this does not
change its hash input. Leaf widths and salts come from candidate opening
slices `[0..480]`, `[480..608]`, `[672..800]` and `[608..640]`,
`[640..672]`, `[800..832]` respectively. No leaf length word is hashed.
A salt is arbitrary, not a fixed suffix separator.

`aspis_core::merkle::node_hash` is a different helper: `11 || left32 ||
right32` (65 bytes); `node_hash4` is `12 || four children32` (129 bytes).
`aspis_core::r0::merkle::parent_with_digest` is the retained eight-way helper:
`18 || eight children32` (257 bytes). These are not the selected R1 binary
multiproof function. Private leaf hashing is reused from
`state_only_private_merkle::private_leaf_hash_with_digest`.

Every listed selected Merkle input starts with 10 or 12, whereas both
initialisation/reseed domains start with ASCII U = 55. Thus none can equal
those frames, regardless of public contents, root, leaf contents or salt.
Node length 65 is also shorter than every semantic public-init input (≥75).
Leaf lengths alone would not suffice for arbitrary public byte lengths;
the prefix proves separation uniformly. Public length is checked to fit u32
and encoded little-endian. `aspis-statement` supplies `Public::public_bytes`
in SPEC §9 order (variant, anchor, nullifier, asset, optional recipient,
change, optional withdrawal amount, source next index/frontier, afterstate
root/frontier); `SemanticTranscript::new` adds the length and C1 root.

## Checked literal refinement and public-init separation

`OracleDecisionDomSepFrozen.lean` independently spells the selected node,
leaf and public-init byte layouts. `shared_node_refines` and
`path_node_refines` identify both existing Lean node encodings with that
layout; `shared_leaf_refines` does the same for leaves. `initial_refines`
identifies `PublicInitFrame.frame` with the literal initial frame (using the
existing explicit four-byte little-endian encoder). These are byte-list
refinements, not proofs of Rust machine execution or public serialization.

`node_not_initial` and `leaf_not_initial` prove disjointness by the first
byte, for arbitrary contents. `node_init_parse_none` and
`leaf_init_parse_none` then prove that `PublicInitParse.parse` returns none
on any address with those exact bytes. No canonical-address enumeration,
large concrete recurrence, or collision assumption is used.

Focused attempt Frozen-1: exit 0, 3.447 s, peak RSS 1,539,686,400 bytes,
zero swaps. All eight theorem axiom reports are subsets of
`{propext, Classical.choice, Quot.sound}`. Exact command, source revision,
source snapshot/hash, import hashes/fingerprint and full outputs are in
`evidence/domsep-20261021/OracleDecisionDomSepFrozen-1/` and `manifest.json`.

## Ordinary transcript frames and the actual obstruction

`BinDecoderInitialStarts.recognizes_initial` proves that public-init frames
start the decoder; it does not characterise **all** recognised starts.
`RecordedBinaryExperimentBin.dec` also recognises semantic absorbs after
recovering their public context from earlier table cells. The term “start”
in `decoderFirstReads` includes these ordinary semantic frames.

For semantic row i the frozen input is
`state32 || 00 || (a0+i) || record_tag || LE32(payload.length) || payload`.
Its length is 39 + payload.length, namely 39, 71, 935, 3751 or 967.
For opening rows the input is
`state32 || 00 || (a0+i) || LE32(payload.length) || payload`.
At S2 the lengths are 966 (y1), 70 (inactive), 262 (round0), 294
(folded root plus round1), 2086 (final message), and 38 (rho). Squeeze and
advance inputs are `state32 || 01/02`, both 33 bytes. The opening reseed is
62 bytes. None is 65, 162 or 514.

`OracleDecisionDomSepSourceFrames.SourceFrameEnvelope` is the union of all
public-init inputs and **every byte string** with one of those non-init
lengths. `node_excluded` and `leaf_excluded` prove exclusion from this
conservative envelope, with arbitrary leaf contents and a 32-byte salt.
The completeness of this source call census is inspected, not an Aeneas
execution theorem. This envelope is not substituted for the current decoder.

The exact overlapping pattern recognised by the current model is

```
node:   12 || 00^32 || a1 || 00^31
absorb: (12 || 00^31) || 00 || a1 || 00^31
```

These are the same 65 bytes. The node has left digest `00^32` and right
digest `a1 || 00^31`. The absorb state is `12 || 00^31`; its domain and
row label occupy offsets 32 and 33, **not** offset zero. Its 31-byte
message is accepted by the model's bounded message codec. A valid frozen
row-one record is exactly `00^5`; its complete absorb is 39 bytes. Thus
there is no colliding pair of valid frozen node and source transcript
inputs here. There is a real overlap with the current decoder's broader
language. Changing a leading node tag alone merely changes the first byte
of the absorb state and does not fix that general overlap.

## Consequences and options for a possible port

1. No protocol modification is needed to separate the selected Merkle
   encodings from valid frozen initialisation frames. That fact alone does
   not establish zero starts of the current decoder.
2. A row-aware decoder could reject all non-frozen message shapes. This is
   a model refinement to investigate, with **zero deployed CU change** if
   shipped code stays fixed. Its density/completion theorem and source
   alignment must be proved before it can replace the existing decoder.
   The source-frame envelope here proves disjointness, not that replacement
   theorem, and is not a hidden extra hypothesis in an endpoint.
3. If changing the protocol were approved instead, a common leading tag
   on **all transcript queries**, distinct from Merkle tags, would give
   separation even for arbitrary state bytes. Merely adding/changing a
   leading node tag does not: the selected protocol already has one.
   An extra one-byte hashv slice would cost 10 additional syscall CU per
   affected call under the locally inspected Solana 4.2.1 default tariff
   `85 + sum(max(10, floor(slice_length/2)))`. Applied to ≤115 transcript
   reads that is ≤1150 extra **syscall** CU. Packing the byte into an
   existing slice instead changes its tariff by 0 or 1 CU, but needs new
   SBF instructions/buffers. Neither estimate includes those instructions,
   and neither is a measured transaction delta or a cluster tariff claim.
   This changes hash outputs, proofs and framing/refinement obligations;
   no such code change or build was made. `cu-analysis.json` pins the
   inspected local runtime sources.
4. Alternatively, keep the current decoder and prove a sharper charging
   argument. The counterexample refutes universal terminal rejection, not
   the aggregate Q+34 bound. Until such an argument or a decoder replacement
   is checked, the existing safe Q+1080 remains the proved start envelope.
   The multiproof call bound 1161 and recorded-log bound Q+2322 are unchanged.

Read-only M10 coordination is recorded in `m10-read-only.json`. Its inspected
ledger still uses Q+1161 as its run-length domain; no adequacy on Q+2322 is
inferred from domain separation. No M10 or concurrent-worker file is changed.

## Compiled obstruction and signature boundary

`OracleDecisionDomSepDecoderObstruction` transports the existing recognised
node through `path_node_refines`. `frozen_node_absorb` gives the exact
literal equality above. `recognized_outside_source_frames` proves, for the
same frozen node and finite supporting table, both exclusion from the source
frame envelope and recognition by the existing decoder.
`leading_tag_overlap` proves the byte overlap for an arbitrary leading tag.

`no_universal_frozen_node_rejection` negates this exact target:

```lean
∀ (cs : BinMerkle32Path.Children) (T : Bytes → Option State),
  RecordedBinaryExperimentBin.dec (OracleDecisionDomSepFrozen.node cs) T = none
```

`frozen_depth18_start` pairs the frozen-node equality with the existing fully
instantiated depth-18 terminal count of one fresh recognised start. Its oracle
agrees with the finite supporting table; its upper padding deliberately uses
collisions. This is not an accepted 57,607-byte frozen proof and is not a
counterexample to a zero-start claim restricted to collision-free accepted
source runs. The unconditional universal rejection target is false; the
aggregate Q+34 statement remains open. No zero-terminal-start theorem or
Q+34 conclusion is asserted in these prerequisites.

No existing Lean module, source verifier, final-soundness endpoint, S-cone
candidate or M10 instrumentation file is changed. `signature-audit.json`
records identical base/current hashes and an empty signature diff for every
existing `R1FinalSoundness*.lean` module, including the requested R19 base.
No premise is removed or replaced, so there is no premise-deletion claim.

## Verification receipts

All compilations used Lean 4.32.0, `-j1 -M4400 -DElab.async=false`, the
shared mkdir lock, and the private `/tmp/codex-cx-domsep-20261021-objects`
overlay. Three final modules pass, with 17 standard-axiom audits and zero
swaps. Every actual attempt has its exact target/argv, parent source revision,
source snapshot/SHA256, dependency hashes/fingerprint, exit, wall time, peak
RSS, swaps, full axiom reports and diagnostics in the committed packet.

| Module suffix | Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
|---|---:|---:|---:|---:|---:|
| Frozen | 1 | 0 | 3.447 | 1539686400 | 0 |
| SourceFrames | 1 | 1 | 1.614 | 1520877568 | 0 |
| SourceFrames | 2 | 0 | 1.521 | 1536573440 | 0 |
| DecoderObstruction | 1 | 1 | 11.605 | 3548594176 | 0 |
| DecoderObstruction | 2 | 1 | 24.311 | 3555835904 | 0 |
| DecoderObstruction | 3 | 0 | 5.709 | 3624796160 | 0 |

SourceFrames-1 failed because `simp` had already closed the goal before a
trailing `omega`; the redundant tactic was removed. DecoderObstruction-1
and -2 failed on identifier/type resolution (ambiguous Byte, the pad namespace,
and the Table alias), with derivative recursion diagnostics on malformed
terms. The successful source uses explicit `Fin 256`, the correct namespace,
and `Bytes → Option State`; no limit was increased and no unchanged failing
source was rerun. Failed elaborations' diagnostic `sorryAx` reports are not
accepted proof evidence; only the 17 final green audits are accepted.

`audit.py` checks all snapshots, final source/receipt agreement, direct-import
hashes, axiom coverage, source restrictions and unchanged endpoint signatures.
The final focused evidence audit is not a package-wide or frozen release
replay. No generated certificate, runtime artifact, Aeneas cone or SBF program
changed, so none was rebuilt or replayed. No binaries or objects are committed.
The genuine obstruction above stops the requested current-decoder zero-start
proof; pursuing Q+34 requires an approved decoder/charging argument, not a
larger build or more normalization.
