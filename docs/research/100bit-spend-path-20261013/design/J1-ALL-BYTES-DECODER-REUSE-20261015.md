# All-bytes decoder reuse inventory

This note records checked interfaces that may be useful for instantiating a decoder on the literal byte-address sampler. It is an API inventory, not a decoder construction or a security conclusion. In particular, the byte address space remains `Bytes` with no global maximum-length restriction.

## Checked generic laws

`AspisV8R19.OracleFiniteSupport.support` in [`OracleFiniteSupport.lean`](../../v8-full-view-zk-20260912/lean/AspisV8R19/OracleFiniteSupport.lean) is a finite set of all potentially queried addresses of a finite `Program I A O`, including every answer branch. Its `finite_support_oracle_law` theorem assumes `[Fintype A]`, `[DecidableEq I]`, and `[Nonempty A]`; for `support p ⊆ s`, a fallback answer, and any observation, it equates a finite uniform table on `s` with `lazyMean p (fun _ => none)`. `finite_support_law_independent_of_fallback` shows the finite-support mean is independent of the chosen fallback.

[`CachedFiniteSupport.lean`](../../v8-full-view-zk-20260912/lean/AspisV8R19/CachedFiniteSupport.lean) retains an arbitrary initial table. `cached_law` states that, under the same finite answer and address-decidability assumptions and `support p ⊆ s`, the mean of `eval (complete t (extend s H fallback)) p` equals `lazyMean p t observe`; `own_support_law` specializes to `s = support p`. This models lazy cached answers on arbitrary address type `I`. It does not impose a bound on byte-string length; finiteness is on the program’s potential support, not on all of `I`.

The generic FS reduction is [`R0C/V3/Gen.lean`](../../v8-r0-close-20261007/lean/R0C/V3/Gen.lean), theorem `R0C.V3.lemmaA3`. It assumes an arbitrary `Dec` decoder over `I`, a rowwise `blaw` bound `ε`, and `FirstReadsBound q t N`; it concludes `lazyMean q t (indicator (hitsChain3 dec bad t ·)) ≤ N * ε`. Its type requires `[DecidableEq I]`, `[Inhabited A]`, `[Fintype A]`, and `[Nonempty A]`, but not `[Fintype I]`. It is a reusable reduction once a suitable decoder and first-read bound are supplied; it does not itself produce those facts for the literal byte decoder.

## Bounded selected-address decoder and canonical labels

The checked selected-address decoder is [`UnifiedDecoder.lean`](../lean/UnifiedDecoder.lean), `AspisR1.UnifiedDecoder.decode`. It dispatches to the initial, semantic, reseed, opening, query, and rho decoders by parsing the row label; `decode_sound` only says a successful result comes from some row `n < 33`. The component APIs and their bounds are also exposed there. Its address type is `Addr L`, not unrestricted `Bytes`, and its input table is `Table (Addr L) State`.

The address wrapper [`CanonicalAddressEmbedding.lean`](../lean/CanonicalAddressEmbedding.lean) defines `AddrC L := {a : Addr L // CanonicalByteAddress.Canonical a}` and proves `toBytes_injective`, `bytesEmbedding`, and `image_length_le`. The canonical-label result [`UnifiedCanonicalLabels.lean`](../lean/UnifiedCanonicalLabels.lean), theorem `samp_allLabels`, proves that every query in every continuation of the selected `UnifiedSampler.samp` program is canonical. This fact concerns that sampler’s addresses. It is not an all-label theorem for an arbitrary adversary program.

[`ProgramLabelRestriction.lean`](../lean/ProgramLabelRestriction.lean) defines `AllLabels` and `restrict`; `rename_restrict` proves that restricting a program to a subtype of permitted labels and renaming back recovers the original program when every continuation satisfies the label predicate. This provides a structural way to move a program whose asks are known to be canonical into the subtype `AddrC L`.

The selected decoders are already proof-relevant but remain bounded-address models. For example, `UnifiedSemanticDecoder.decode_sound` recovers a parsed context and `UnifiedQueryDecoder.decode_sound` recovers a 31-record opening context. These interfaces do not directly accept arbitrary byte strings or prove equivalence to the selected sampler over all byte inputs.

## Unrestricted byte sampler and independent-answer transport

[`LiteralByteSampler.lean`](../lean/LiteralByteSampler.lean) defines `LiteralByteSampler.samp` over `Bytes`. It maps each selected `Addr L` query to its exact `Addr.toBytes`; it has no fallback for overlength addresses. `eval_eq` relates its execution to `OracleProgramOps.mapView Addr.toBytes`, and `independentMean_eq` transports independent-answer means through `ProgramSamplerMap.independentMean_map`.

[`ProgramSamplerMap.lean`](../lean/ProgramSamplerMap.lean) defines `fromProgram` and `map`. Its `toProgram_fromProgram` theorem identifies the sequential sampler’s program with its source program; `independentMean_map` proves independent-answer mean invariance under an arbitrary label function `I → J`. The module comment correctly limits this to independent-answer means: it does not establish preservation of `follow`, first-read behavior, or shared-oracle injection.

That distinction matters because [`LiteralByteProtocol.lean`](../lean/LiteralByteProtocol.lean) uses a `Decoder` with type `Bytes → Table Bytes State → Option (Sampler Bytes State ...)`, while the selected decoder expects `Addr L → Table (Addr L) State → ...`. `LiteralByteProtocol.d1` and `d2` are generic in that decoder; the module explicitly leaves decoder injection, D3, and a Merkle compiler open. The D1/D2 results therefore do not instantiate the bounded selected decoder on all byte strings.

## `Sampler.multi` versus `BS.spawn`

[`FS2/Statement.lean`](../../v8-fs-generic-20261006/lean/FS2/Statement.lean) defines `Sampler.multi c cs nd k` as a nonempty duplicate-free set of predetermined addresses. Its continuation receives an answer function over addresses, and `Sampler.toProgram` converts it to sequential reads in list order. `FS2.follow` instead accepts reads in any order for that multi-set, requiring first reads for the requested cells.

[`R0C/V3/BS.lean`](../../v8-r0-close-20261007/lean/R0C/V3/BS.lean) defines a different object: `BS` has `.done`, `.ask`, and `.spawn`; `bfollow` tracks pending `(address, Option answer)` entries, calls `pushSpawns`, and checks `waits` against the observed trace. Thus `BS.spawn` records deferred obligations in the background-sampler representation, whereas `Sampler.multi` groups an already determined, duplicate-free collection of address reads with an order-insensitive answer-function continuation. They are not definitionally identical, and the existing independent-mean label-map theorem does not bridge their follow semantics.

## Missing adapters recorded by this inventory

The available pieces leave the following concrete connections unproved here:

- a decoder on unrestricted `Bytes` that agrees with the selected decoder on the canonical image, with an explicit policy for noncanonical and overlength inputs;
- transport of successful decode results, pending reads, and follow/bfollow across `Addr.toBytes` (independent-mean transport alone is insufficient);
- a first-read/injection theorem for the mapped unrestricted-byte program, including preservation of address equality only on the canonical subtype;
- compatibility between the `Sampler.multi` first-read semantics and any `BS.spawn` obligations used by the selected decoder’s reduction;
- an all-bytes decoder correctness/coverage statement and its accepted-execution terminal implication.

No theorem in the cited modules supplies a global byte-input length cap, a first-read injection result for arbitrary byte programs, or a complete all-bytes decoder instantiation. These remain separate interfaces to establish or explicitly leave open.
