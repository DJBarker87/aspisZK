# Literal J1 density and D1/D2 checkpoint

This is a checkpoint for the literal-message sampler model, based on the focused Lean evidence bundles listed below. It records sampler-density and generic protocol facts only. It does not claim the R1 source/Pool path refines this model.

## Checked result

`AspisR1.LiteralClassifier.density` proves a bound for every row `i < 33`, every literal prefix `P`, and every current literal message `m`, with the event and row budget selected by `P.round`. The row partition is concrete:

| Rows | Density input | Budget used by the classifier |
|---|---|---|
| 0–24 | `LiteralSemanticDensity.event ConcretePackBasis.basis` | `R0P.Mask.combinedD2BudgetZ i` |
| 25–26 | the two literal circle rows | `LiteralCircleDensity.budget = (1 + deltaQ) / P^4` |
| 27 | gamma opening | `336869026622539 * OpeningSamplerBound.gammaAtom` |
| 28 | kappa opening | `600 * OpeningSamplerBound.atom` |
| 29–30 | first/second opening folds | `9396508281846 * OpeningSamplerBound.atom` |
| 31 | selected-query row | `UnifiedQueryDensity.queryCap` |
| 32 | rho residual row | `RhoSamplerBound.rhoCap` |

The proved conclusion is a row-wise `independentMean` bound, not an aggregate numerical security estimate. The query reader projects only a successfully decoded, duplicate-free, length-22, in-range query list into `Fin 22 → Fin 262144`; a separate theorem identifies its old set-valued challenge set with the image of that ordered view. The rho row reads matching data and that query list from the completed prefix. Circle row 26 reads the row-25 ordinary challenge as its fixed prior point. The opening and semantic row callbacks likewise use literal entries fixed before the fresh challenge. If one of these local readers returns `none`, its corresponding event is false. This fact alone does not prove that an admitted execution has a successful reader.

The concrete literal classifier is lifted to a byte sampler in `LiteralClassifier.byte_density`. `LiteralByteProtocol.d1` and `LiteralByteProtocol.d2` then establish D1 and D2 for a 33-row protocol over unrestricted byte inputs, for any explicitly supplied decoder. The extractor in this protocol is `GenericNoHit.chooseWitness`, a specification-level choice extractor. These results do not establish D3, a decoder first-read/injectivity theorem, a Merkle compiler, an executable efficient extractor, or a ZK theorem.

The row families also depend on checked support bounds imported by the classifier: `LiteralSemanticDensity` source SHA `6993a63eded708aaab9f9dee8d89e4dce1916bec877d482d39a53e3c2aba3c3c` (object `aa43a581fc506626705387f4edeaacdec948bc89311f5d1b57a0a03ea7b3b005`, 1.73 s, 3,596,228 KiB, one standard-axiom report), `LiteralCircleDensity` source SHA `e353554ab952041f34a53113b62840b319c7f41acb073ee81949e8701769e302` (object `4e65dc440bdd66b99a71ec1a47a84d431fd618cb67ad45c6294c87a4a3da5d50`, final attempt e, 1.83 s, 3,587,676 KiB, five standard-axiom reports), and `LiteralOpeningDensity` source SHA `32ba2a1e313e8751d65183afea7d218341477a3758b3a6c0b8431d863f4d9250` (object `604c4b1494ebbec43d53be0ca30eff75a1cfbe712f71e2f08b3209c1fd619d6b`, 1.69 s, 3,594,936 KiB, eight standard-axiom reports). Their pinned evidence is respectively [semantic density](../evidence/lean-literal-semantic-density-20261015/README.md), [circle density](../evidence/lean-literal-circle-density-20261015/README.md), and [opening density](../evidence/lean-literal-opening-density-20261015/README.md). The generic literal ordinary-row lift has source SHA `7239850e2b77fd77091c3f2ec6b89d20f975b9755eb89dda90d594b784aa2ec0` and object SHA `29428a9cdc3f9364d36dba1cb06a935e90c465a08e755e94094d7213f14b6fbf`; its evidence is [ordinary density](../evidence/lean-literal-ordinary-density-20261015/README.md).

The key change in the event construction is that each row's callback is computed from the literal prefix and current message before that row's fresh sampler answer. For example, the row-31 query set is read from already fixed literal records, and row-32 reads its query list from the completed row 31. This removes arbitrary external word/function selectors from these density callbacks. It does not establish accepted-reader coverage, that the source protocol generates the modeled literal messages, or that the source/Pool execution reaches the callbacks with the required successful reads.

## Evidence pins

All Lean targets below were compiled with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. Hashes are SHA-256. The source/object/archive and complete attempt records are in the linked bundles; failed attempts remain recorded there.

| Target | Final source SHA-256 | Final object SHA-256 | Focused compile (attempt; wall; peak RSS; reports) | Evidence |
|---|---|---|---|---|
| `R1LiteralCircleEvents` | `1e0e0ef18c92ac80fe83e83c9219f5eade6bf63c39a14a1f2a9bb710213eee64` | `50d6fee195416236bbc4766d2f1388984d8ae6a3b8cd828a65c5addfab1d45fb` | b; 1.78 s; 3,578,692 KiB; 3 | [circle events](../evidence/lean-literal-circle-events-20261015/README.md) |
| `R1LiteralMatchingData` | `abc312f7b2df337d96c97ebb4e8aab8eab70324d204751daf488d3e4206602b3` | `9a162b010fbcc1db205a79a4cec3a4a79742362bbe76f42cb11ecfaead591003` | a; 1.67 s; 3,571,328 KiB; 1 | [matching data](../evidence/lean-literal-matching-data-20261015/README.md) |
| `R1LiteralQueryRead` | `263749fb06146088318eee7c37d44b7c8ee31dd68e559419e85a35976554622e` | `ef097dacb04fc69287c23a4ea372f727d61c77584176e952ed15c3eb27228157` | b; 1.59 s; 3,571,068 KiB; 2 | [query reader](../evidence/lean-literal-query-read-20261015/README.md) |
| `R1LiteralQueryReadFacts` | `c2f39a5a7b0413d62fbf1bffab2ecb676340e77aae2906217ffef2467ad86cd4` | `8b3a9b3e035f6e507155d6ba0f277fefe9de2855d4d2bbc255c14adffd4d7b7f` | b; 1.53 s; 3,569,104 KiB; 2 | [query read facts](../evidence/lean-literal-query-read-facts-20261015/README.md) |
| `R1LiteralQueryDensity` | `bca87f959d1cf6a8ec41c4953915a6a1ac941ebb9b717ebd39f21e4b8a90d59d` | `f4145ec03d3848e9b31d584d4e6e6456f1bc5086d2f82390a63325129fbdc609` | b; 1.64 s; 3,601,616 KiB; 1 | [query and rho density](../evidence/lean-literal-query-rho-density-20261015/README.md) |
| `R1LiteralRhoDensity` | `a94b5dff6d56365c7c2c2438d332324db1e33a91dd6098887384d3c3a4dda0be` | `b447d0cdb875fe36312eb0c3034a1b607a70697fefd40018234767f1a6b1fda8` | a; 2.12 s; 3,598,952 KiB; 2 | [query and rho density](../evidence/lean-literal-query-rho-density-20261015/README.md) |
| `R1LiteralClassifier` | `07b31cfc4be5c613fcdd444bef9ff51519846b8fed202b1927d99e84ace1efb8` | `5879ea5c61506183b2a633778aef606e9d9ba302da2950e884bea48b78c5194a` | b; 1.73 s; 3,615,544 KiB; 2 | [classifier and byte protocol](../evidence/lean-literal-classifier-20261015/README.md) |
| `R1LiteralByteProtocol` | `127011d62beb6d8b184ddc7ebe81151c2d211982a2f1705fc8bd6b14297bf503` | `5d04d4dfb92fdc801dbd0caf7ab1021461abecce2ae10c37f6e17690574ae840` | a; 1.51 s; 3,608,520 KiB; 2 | [classifier and byte protocol](../evidence/lean-literal-classifier-20261015/README.md) |

Each successful public theorem audit reports only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound` (some deterministic query-read declarations omit `Classical.choice`). No failed-attempt report is counted as a successful audit. The failed attempts and their diagnostics are retained in each bundle.

Three auxiliary targets are checked in the same checkpoint: [indexed no-hit facts](../evidence/lean-generic-no-hit-index-20261015/README.md), [append stability](../evidence/lean-literal-read-stability-20261015/README.md), and [query-context coherence](../evidence/lean-literal-query-context-20261015/README.md). Together they add eight standard-axiom reports, for eleven targets and 23 reports overall. The query-context theorem proves that drawing the row-31 challenge cannot change the matching data, and that row 32 reads exactly the same data. These are deterministic coherence facts, not accepted-reader coverage. The [lead audit](../evidence/j1-literal-d2-lead-review-20261015.json) records their exact source, object, resource and axiom pins.

## Serializer extraction boundary

The separate [public serializer extraction evidence](../evidence/public-serializer-extraction-20261015/README.md) does not close a source link. Attempt **a** had outer exit status 0, but Aeneas emitted no ordered declarations usable for the serializer proof (`empty_no_ordered_declarations`; no meaningful serializer emission). Attempt **b** exited 2 during Aeneas translation with an `Unreachable` exception in the loop over `after.next_frontier` (source lines 239–243); it emitted no usable Lean translation. Preserve these as extraction outcomes only. They do not contradict the checked equality between the two Lean public-wire models, and they do not establish the source Rust serializer's refinement to either model.

The two configuration probes preserved the same Rust source and also failed at that loop: [attempt c](../evidence/public-serializer-extraction-c-20261015/README.md) used `-loops-to-rec` on the same LLBC, and [attempt d](../evidence/public-serializer-extraction-d-20261015/README.md) used optimized MIR without monomorphization. Their failures remain separate evidence; neither emitted a usable serializer translation.

## Remaining gates

The all-row density theorem and D1/D2 protocol statements are not the missing end-to-end result. D3/terminal accepted-execution implication, successful-reader coverage on accepted executions, decoder first-read injectivity, a Merkle compiler, correspondence to the current Rust/Pool program, an executable efficient extractor, and a zero-knowledge theorem remain open.
