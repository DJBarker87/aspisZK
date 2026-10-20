# Shared binary record grammar (2026-10-20)

Branch `codex/cx-shared-grammar-20261020`, base `96906b19032823e349368f75b39f5d9922d3c3d9`.
Only three new Lean modules are added; existing Lean statements and frozen
verifier sources are unchanged.

## Module of record and equality bridges

`docs/research/100bit-spend-path-20261013/lean/SharedBinaryRecordGrammar.lean`
is the unified-base import `SharedBinaryRecordGrammar`, selected as a spend
source by the same manifest rule as the existing spend-path imports. It defines
`0x12 ‖ left ‖ right`, `0x10 ‖ tree-tag ‖ values ‖ salt`, the three tree tags,
semantic row tags/payload widths, four opening widths, semantic framing and the
fixed-width privacy wire carrier. The byte-polymorphic Merkle constructors
support both `Fin 256` and `UInt8`.

The D79 addendum's `BindingClass`, `BindingRecord`, `CheckpointBody` and
`Tx1Class` are **aliases of the existing `WireBindingRecordCodec`**, including
its size and byte functions, rather than a second copy of their definitions
or proofs. This preserves the exact checksum constructor (domain + typed
body), compact proof 57,607, ASF8 1,880 and checksum input 1,758. The full
`Tx1Class.size` inventory (including the 65-byte node, 514/162-byte salted
leaves and all transcript classes) is available through `classSize`;
`class_safe` directly reuses the existing non-node separation theorem.
Semantic payload widths are 0/32/896/3712/928, opening widths are
928/32/224/256 and final data is 2048 bytes. Public bytes remain unrestricted.

* Privacy: `lean/R1Z/SharedGrammarBridgeBin.lean`, namespace
  `R1Z.SharedGrammarBridgeBin`, proves
  `LayoutR1PBin.nodeBytes rest ch = SharedBinaryRecordGrammar.nodeInput
  (fun j => rest (ch j))` (`node_eq`). `treeTag_eq` and `leaf_eq` identify
  the leaf prefix/payload/trailing-salt layout. `semanticSize_eq`,
  `semanticTag_eq`, `openingSize_eq` and `framed_eq` identify the complete
  `WireLengthsR1PBin` tables/framing. `toShared`/`fromShared` have both
  round-trip equalities, preserving every wire field. The existing
  `framed_safe` and `node_ne_binding` results transport to the shared
  definitions without reproving length/separation.
* Soundness: `docs/research/100bit-spend-path-20261013/lean/BinSharedGrammarBridge.lean`,
  namespace `AspisR1.BinSharedGrammarBridge`, proves
  `BinMerkle32Path.nodeInput cs = SharedBinaryRecordGrammar.nodeInput cs`
  (`node_eq`, using the existing `BinGrammar.nodeInput_slices`) and the
  corresponding `BinMerkle32Leaf.leafInput` equality (`leaf_eq`).
  `node_uint8_eq` and `leaf_uint8_eq` additionally prove equality after
  mapping each soundness byte through `b.val.toUInt8`; this explicitly joins
  the two byte carriers, preserving child order. `class_eq`/`binding_eq`
  are definitional identifications of the retained codec. Existing node
  length and node/leaf separation proofs transport by rewriting.

## Unified manifest and verification

`t2b2b/build-integration/manifest-5-shared-grammar.json` retains every
manifest-4 root and adds the shared module, both bridges and the four binary
privacy roots. Its 493 modules pass the manifest generator's `--check`
(no conflicts/unresolved imports). J's post-build audit finds all 493 source
hashes match, every object/library exists, and no source was replaced.
Six previously absent soundness sources were installed, then compiled in
import order; `shared-grammar-build/install-receipt.json` records them.
This is focused verification on the pinned unified cache, not a new full
493-module replay or a new release-coherence claim.

Env J used only attempts **6400–6411**, the existing `run-joint.sh`,
`-M7000`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and its
reservation check/global lock. Successful new targets:

| Target | Attempt | Exit | Wall | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|---:|
| SharedBinaryRecordGrammar | 6400 | 0 | 0.75 s | 1,474,800 | 0 |
| R1Z.SharedGrammarBridgeBin | 6401 | 0 | 1.61 s | 3,485,032 | 0 |
| BinSharedGrammarBridge | 6411 | 0 | 0.81 s | 1,474,900 | 0 |

The five existing soundness prerequisites passed at 6406–6410. All 55
successful J axiom reports (21 for the three new modules) are subsets of
`{propext, Classical.choice, Quot.sound}`. Requests for `R1Z.FinalR1PBin`
(6402), `R1Z.PrivacyR1PBin` (6403), `R1Z.PrivacyBoundR1PBin` (6404) and
`R1J.PrivacySamplerSpendBin` (6405) each exited **67**, refusing the
unchanged source/dependency fingerprint before Lean ran. No refusal was
bypassed. The additive bridges introduce no changed dependency of those roots.

Local final shared/bridge compiles passed with pinned Lean 4.32,
`-j1 -M4400 -DElab.async=false`, private `/tmp/cx-shared-grammar-objects`,
the shared mkdir lock and executable-name memory gate: 2.511 / 6.760 s,
1,271,054,336 / 1,270,874,112 peak RSS bytes, zero swaps, nine standard-only
audit lines. One intermediate carrier-map attempt failed only because two
tiny literal conversions (`UInt8.ofFin 18/16`) needed explicit `rfl` after
list rewriting; its failed log is retained and excluded from final audits.

Evidence (soundness research directory):
`evidence/shared-grammar-20261020/{manifest.json,local-audit.json,j-attempts.jsonl,j-audit.json}`
and per-attempt local/J logs. Each request records source revision parent,
source SHA, dependency fingerprints, command, status, wall/RSS/swap and full
axiom output; refusal metrics are unavailable because no process ran.
J object artifacts are represented by SHA-256 and size only.

## Scope

The grammar ownership and byte-carrier equalities are proved, with existing
proofs carried across by rewriting. Both trees import the shared module through
the new bridges; frozen modules remain unchanged. The existing binding codec
is an explicitly reused dependency of the module of record. This does not
establish Rust execution membership in the typed classes, whole-tx1/tx2
simulation, execution-log correspondence, deduplicated batch transport,
normalisation or the remaining R-wire/R13 premises of D80. No verifier,
Rust/SBF artifact, wallet or key changed; no runtime gate was rerun.
