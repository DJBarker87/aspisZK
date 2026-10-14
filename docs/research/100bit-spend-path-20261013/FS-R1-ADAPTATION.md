# R1 Fiat–Shamir adaptation: exact reuse boundaries

This is a root-owned implementation plan and dependency audit at base
`e8b1a73c6e3fd764ca01701c9c936cd705ce74b1`, not a Fiat–Shamir theorem.
The generic FS2 first-read framework and per-round sampler interface remain
reusable. The old concrete masked instance is not the actual R1 protocol.

## Facts that prevent a round-count-only substitution

1. R1 has 33 challenge rows. Its q22 sampler is row 31 and rho is row 32.
   `MaskProtocol.combinedSamplerAt last` uses a single squeeze before `last`
   and q22 at/after it. `MaskDuplexDecoder.combinedNsteps rounds i` likewise
   assigns eight pairs only at the final row. Instantiating those definitions
   at 33 would place q22 at the wrong row.
2. The old backward `Duplex.walk`, records and `completeRounds` model one
   advance per earlier round. With rho after q22, the decoder must recover
   an earlier multi-pair query round, including all its squeezed blocks.
3. R1 computes all eight query pairs, but `queries_from_pairs` resumes from
   the advance where the bounded scan stops. That may precede the eighth
   advance. `Q22.scanOut` and `DQ.out4` already model this selected state.
   The old q22 law must not be silently changed to an eighth-state law.
4. The R1 row-25 payload includes 87 point claims and 29 extra claims.
   The old typed context carries the extra vector from the start. The new
   message model must bind the actual later payload. A byte encoder cannot
   silently drop adaptive fields while retaining an injectivity premise.
5. Row 27 transmits only the 29 y1 values. The other opening claims belong
   to earlier messages; a synthesized algebraic opening view must preserve
   that chronology without pretending it was all transmitted at row 27.
6. `Transcript::new` hashes the P3 domain, variant and semantic state at
   the semantic/opening boundary. The current generic direct-duplex walk
   does not account for that extra hash edge. Initial public/C1 binding is
   also outside the challenge-row table. Source correspondence must include
   both operations and their oracle-read accounting.

The ten central Rust source hashes from `TRANSCRIPT-R1-INVENTORY.md` were
rechecked unchanged at the preceding base. The inventory describes the
unproved cost probe; no protocol or runtime source was changed here.

## Reuse without a future-message premise

`SemanticContext.withExtra` changes only the legacy context's extra vector.
The C2 word construction and `semanticBadZ` are definitionally unchanged.
`SemanticContextPrefix.no_hitFrom_withExtra_iff` reuses the existing indexed
prefix characterization to prove that the entire parsed prefix no-hit event
(up to 25 rows) is unchanged. Thus a fixed placeholder can be used for these
early classifiers. This result does not identify the old opening decision
with R1's decision, and does not by itself establish a causal oracle law.

## Recovery route under review

Preserve the actual selected-state q22 behavior. Reuse the old no-collision
lemmas to recover unique advance predecessors; recover the query absorb
boundary by following those predecessors. Recover the complete eight-pair
spine from table lookups, even when the subsequent rho absorb starts at an
earlier selected advance. A prefix-completion record must store enough of
that spine to enumerate all earlier missing squeeze cells and reconstruct
the q22 challenge from the existing `scanOut` definition.

The current focused lemmas establish only deterministic pieces: advance
rewinding under the existing no-collision/table premises, and membership of
the selected query state among the eight advances. The full decoder still
needs to discover the correct boundary, handle the domain-transition edge,
complete missing cells with the correct law, and satisfy the generic
first-read/injection obligations. In particular, state membership alone is
not a decoder or an independence theorem.

After that, the actual message parser, the R1 per-round bad events and
D1/D2/D3 composition remain to be instantiated. The current algebraic
candidate and input/output-state extraction can supply the deterministic
semantic endpoint. Authenticated-word/source correspondence, account guards,
shared-oracle collision accounting and privacy remain separate obligations.

## Checked increment

The following six focused targets are green:

| Target | Exact contribution |
| --- | --- |
| `R1SemanticContext` | Replacing only `extraClaims` preserves C2 words and the semantic classifier. |
| `R1SemanticContextPrefix` | The parsed first-25-row no-hit event is invariant under that replacement. |
| `R1DuplexRewind` | Unique advance-predecessor lookup and finite rewinding, derived from the old collision/table lemmas. |
| `R1QueryContinuation` | The actual selected state belongs to the eight advances, including early stopping. |
| `R1QueryRecovery` | Some selected index below eight has a correctly recovered predecessor path under the unchanged collision/table premises. |
| `R1FSReuseCheckpoint` | Combined import and ten axiom audits. |

The combined checkpoint passed in 1.37 seconds at 3,557,136 KiB peak RSS,
zero swap. All ten axiom reports use only `propext`, `Classical.choice`
and/or `Quot.sound`. This check composes the deterministic lemmas; it does
not yet instantiate a probability theorem or discover a decoder boundary.
Each target ran on the pinned NUC with 4G/6G/0 high/max/swap caps. Source,
failed attempts, receipts and compiled objects are retained in
[evidence/lean-fs-reuse-20261014](evidence/lean-fs-reuse-20261014/README.md).

## Hash-edge reuse inventory for the next step

Root inspected the older generic `UniformFrameCollision` and
`CausalInjectiveFrameBound` modules after a read-only inventory. They accept
an arbitrary injective state-to-address frame, and the causal theorem
allows the frame and prior-read list to depend on the preceding tape
prefix. They do not permit dependence on the current or future tape cell,
and do not instantiate the R1 source callback.

The concrete `FS2.Duplex.badColl` instead checks equality with a fixed IV,
earlier outputs, and the first 32 bytes of earlier/current addresses.
`Params.iv` is a value, not a function of the oracle. The R1 public/C1
initialization query and the reseed query with its trailing state bytes
therefore require explicit modeling and an appropriate causal frame
connection. Neither is supplied by setting `iv` to a hash expression in an
otherwise unchanged fixed-IV theorem. The generic frame results are reuse
candidates, with their source and first-read premises still to be proved.

All 14 Rust source/manifest fingerprints in the source inventory were
independently rechecked unchanged during the root audit. No source or CU
claim is inferred from these Lean structural checks.
