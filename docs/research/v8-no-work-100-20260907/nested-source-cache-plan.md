# Nested source refinement: minimal V7 reuse plan

Read-only plan at research parent `d0e3196848b89de8ddf1a85fcc0a6e55bf8fdc95`,
borrowed V7 `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. No build, cache append,
manifest mutation, production edit or old proof replay was performed.

## First leaf: no new cached imports

Import `NestedCircleRouting` and the already-pinned
`AspisFormal.K1.V7Tag73SamplerDecoderExact`. Port only these attributed bodies:

| V7 source | Slice | Required declarations |
| --- | --- | --- |
| `V7Tag73VariablePrefixGammaSampler` | 76–262 | `decodeLimb_take_attemptsUsed`, `decodeLimbs_take_wordsUsed`, `flattenedWords_take_blocks`, `decodeOrdinaryPrefix_take_blocksUsed` |
| `V7Tag73VariablePrefixGammaFlatRouting` | 658–675 | `decodeOrdinaryPrefix_of_matching_consumed_prefix` |

Sampler source SHA-256:
`5395e710e188f1f7e2085fbf84304fd040215446be7349d75061a540e22dea1f`.
FlatRouting source SHA-256:
`f99a9cd8160535f3bab41c6bb87bc775ff7d39cabe431b00aed1a0981f214041`.

The trim proofs use the already-checked first-accepted decomposition and
constructor in `SamplerDecoderExact`, plus `decodeLimbs_append_of_some` in
`IncrementalSamplerControl`. Matching-consumed-prefix uses the trim theorem,
the already-pinned `decodeOrdinaryPrefix_append_of_some`, and list take/drop.
Its `targetLong` premise is unused in the old proof body; retaining that
interface is harmless but not necessary to reconstruct the proof. No gamma,
semantic transcript, nonzero-wrapper or q16 theorem is needed here.

The ordinary trim keeps unused words in the last consumed block and removes
later whole blocks. It is not a fixed-four-block alignment theorem. A useful
new bridge is:

```text
decodeOrdinaryPrefix pending = some decoded
every strictly shorter block prefix of pending returns none
⇒ decoded.blocksUsed = pending.length ∧ decoded.remainingBlocks = []
```

The existing trim theorem gives a successful prefix of length `blocksUsed`;
minimality excludes a shorter cut, and the checked source-tail theorem gives
the empty remainder. The controller must derive this minimality from its
chronological need-more execution, not receive it as an unexplained final
source-correspondence premise. This is the missing no-unread-whole-block
invariant needed before `afterOrdinary` can safely discard its pending buffer.
Then compose actual first-circle3 and distinct3(circle3) on the returned tails.

The old files set `maxRecDepth 10000`. A narrow port should not carry that
module-wide setting: reuse their symbolic proof structure under the current
focused budget and isolate any local elaboration problem before a retry.

## Later router: six compatible local pairs available

`PreAnswerSlotMachine.fullCoordinateEquiv` is genuinely generic in Output,
Slot, State and residual length. Its q16-named import path does not impose q16
on a new slot type. Prefer reuse of the following exact local closure after
a separately authorized append, in dependency order:

1. `AspisFormal.V5BoundedQuerySamplerUniformity`
2. `AspisFormal.K1.V7Tag73Q16FirstCompactUniformity`
3. `AspisFormal.K1.V7Tag73Q16DigestDrawReindex`
4. `AspisFormal.K1.V7Tag73Q16CompilerTapeCoordinates`
5. `AspisFormal.K1.V7Tag73CausalQ16CoordinateRouter`
6. `AspisFormal.K1.V7Tag73CausalSlotMachineRouter`

All six local sources match borrowed26a9, all outputs have pinned Lean 4.32
headers, and their retained local traces have no errors and standard-only
axiom audits. All three cut-boundary pairs match the frozen overlay exactly:
`V5WithoutReplacementQuerySoundness`, `V7Tag73DeployedDecoderFiberCap` and
`V7Tag73ExactCompilerResources`. Full source/output/trace hashes for every
module and each boundary are in `nested-source-cache-plan.json`.

The final router module source is
`322f244628ed458a3e740f4a7df10314438d80e665f98522b6f376dc5d364100`;
local olean is
`008fdc84a1015e48ceb0e2df6d73a617b8c7ce50670ef94ae174f211da7f6a7e`.
Its predecessor's generic `coordinateEquiv` recursively erases one chosen
special slot or consumes one residual coordinate before revealing the answer;
the inverse replays those choices. `fullCoordinateEquiv` then transports the
universal finite slot set to a function on Slot.

An alternative source port needs the generic part of
`CausalQ16CoordinateRouter` (38–178) and the machine constructor file, against
already-pinned `AdaptiveLazyOracle.FreshAnswerTape`. It can omit the q16 forest
specializations and compiler-resource endpoints. This is more new proof
surface than six verified local pairs, and neither route is required for the
first locality leaf.

The router does not certify source labels automatically. A repeated preferred
slot is sent to residual coordinates, and when residual capacity is exhausted
the constructor fills an unused special slot by its fallback rule. Thus the
consumer must show meaningful source reads request still-unfilled slots, and
that fallback fills are genuine post-halt/unread padding. Halted-state
stability prevents ghost answers changing the source result. The 48 output
slots do not account for paired duplex-advance coordinates by themselves.
No q16 query count, 512-slot endpoint or q16 probability bound transfers to
the q22 protocol merely by importing this generic module.

## Why not copy the native cache wholesale?

The retained comparison manifest is NestedCircleRouting v3, 871 entries,
SHA-256 `8b333315f2dcd4a9aac362f4cb064a03340c4d5deb35bb6fcea87b14cc1a0c80`.
The existing scope keeps its creation parent289d distinct from source parentd0e.
Traversal stops at exact overlay source/output pairs and external packages.

| Full imported root | Missing module pairs | Cut boundaries | Native boundary olean differences |
| --- | ---: | ---: | ---: |
| VariablePrefixGammaSampler | 33 | 17 | 12 |
| VariablePrefixGammaFlatRouting | 35 | 18 | 12 |
| CausalSlotMachineRouter | 6 | 3 | 1 |

All inspected local source blobs and all local cut-boundary output bytes match
the pin/overlay. The larger sampler closures are available locally too, but
are unnecessary for five locality facts. The native differences are byte
variants, not evidence that the mathematical theorems are false; unverified
variant mixing remains unacceptable.

The native router boundary `V5WithoutReplacementQuerySoundness` has olean
`7247f01d…`, whereas the frozen/local variant is `2498f029…`. Native
`V5BoundedQuerySamplerUniformity` also differs from the matching local new
pair. Native `ExactCompilerResources.lean` has drifted to `c177acab…` while
the pinned source is `31cf28ec…`, despite its olean retaining the same bytes.
The sampler closure still encounters native `TranscriptSchedule` source
drift. The JSON preserves full hashes and all twelve native sampler-boundary
variants; do not replace these frozen entries or copy current native sources.

NUC inspection used only Tailscale `dombarker@100.108.41.90`, with pinned
host-key alias `nuc.local`. At the read-only snapshot, 44,650 MiB was available
and no user build scope was listed; unrelated services and host swap were
untouched. Local artifact compatibility here means checked graph/source/output
bytes and historical traces, not a newly compiled mixed-overlay import test.
Any future append needs a fresh reservation and before/after receipt; its
first changed consumer remains the focused native import check.

No new theorem or probability credit arises from this plan. Full nested source
refinement, the finite-tape or stopped-prefix law, adaptive OOD composition,
and actual Fiat–Shamir coupling remain distinct subsequent obligations.
