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
