# J1 sampler/configuration reuse inventory

This is a read-only inventory originally recorded at source revision `136b746805f3438507732622c9b4e50f36bf49f9`. The sampler-chain addendum below was revalidated against worktree HEAD `764bf20a6fe0392951b670f73748a54f70c9f272`; its individual SHA-256 pins are listed below. It identifies reusable finite encodings and the scope of historical sampler results. It does not select a concrete `Params.σ`, prove that R1 Rust uses one of these maps, or make a probability claim for the current transcript.

## Finite encodings already present

The shared duplex model defines `SourceDuplexStep.State := Fin 32 → Byte`, with `Byte := Fin 256`, and `bytes s := List.ofFn s` ([`SourceDuplexStep.lean:11-12`](../../v8-full-view-zk-20260912/lean/AspisV8R19/SourceDuplexStep.lean)). It also proves `bytes_length` at line 20. Thus the exact state type is a 32-vector of byte values. `AspisR1.SamplerRanking.digitsRank p n : (Fin n → Fin p) ≃ Fin (p^n)` and `digitsRank_value` give the generic positional rank and little-endian sum identity ([`SamplerRanking.lean:7-24`](../lean/SamplerRanking.lean)). Instantiating at `(p,n)=(256,32)` yields an equivalence to `Fin (256^32)`; `R0C.ModuloField.blockRank` is that same `finFunctionFinEquiv` at [`ModuloField.lean:19-24`](../../v8-r0-close-20261007/lean/R0C/ModuloField.lean). The old model separately has `UniformStateFirstHit.state_card : Fintype.card State = 256^32` ([`UniformStateFirstHit.lean:32-33`](../../v8-full-view-zk-20260912/lean/AspisV8R19/UniformStateFirstHit.lean)). No named theorem directly states `State ≃ Fin (2^256)`; it follows from the vector equivalence and the arithmetic identity `256^32 = 2^256`.

The retained exact tower declares `P = 2147483647`, `M31Exact := ZMod P`, `CM31Exact := QuadraticAlgebra M31Exact (-1) 0`, and `QM31Exact := QuadraticAlgebra CM31Exact (2+i) 0` ([`ExactTowerBase.lean:12-17, 101-102`](../../v8-full-view-zk-20260912/lean/AspisV8R15/ExactTowerBase.lean)). `R599CanonicalFieldTuple.tupleFieldEquiv : (Fin 4 → Fin P) ≃ QM31Exact` provides both directions, with `fieldTuple` extracting the four canonical `ZMod.val` coordinates ([`R599CanonicalFieldTuple.lean:12-37`](../../v8-full-view-zk-20260912/lean/AspisV8R19/R599CanonicalFieldTuple.lean)). `ExactTowerFinite.qm31Exact_card` proves `Fintype.card QM31Exact = P^4` ([`ExactTowerFinite.lean:17-33`](../../v8-full-view-zk-20260912/lean/AspisV8R15/ExactTowerFinite.lean)). The older semantic model has the positional inverse equivalence `R0P.SemSource.qm31Rank : Fin (P^4) ≃ QM31Exact` ([`SemD2.lean:179-184`](../../v8-r0-sem-proof-20261008/lean/R0P/SemD2.lean)).

For the full extension, `R0C.ModuloField.digitsField : (Fin 8 → Fin P) ≃ WideExact` splits eight digits into two quartic tuples, then uses the quadratic-algebra product equivalence; `fieldRank : Fin (P^8) ≃ WideExact` is the base-P positional rank ([`ModuloField.lean:26-50`](../../v8-r0-close-20261007/lean/R0C/ModuloField.lean)). The corresponding field cardinality is `P^8` in the same sampler model. For nonzero outputs, `positiveRanks n hn : Fin (n-1) ≃ {x : Fin n // x ≠ 0}` is defined explicitly at lines 53-66, and `nonzeroRank : Fin (P^8-1) ≃ {x : WideExact // x ≠ 0}` composes that with `fieldRank.subtypeEquiv` at lines 68-74. There is no separately named `QM31Exact` nonzero-rank map in the inspected modules; the same generic `positiveRanks` and the `qm31Rank` subtype equivalence are the reusable pieces. `fieldRank_zero` is the required zero correspondence for the WideExact nonzero construction.

## Existing sampler models and their exact boundary

`R0C.ModuloField.ordinary s` maps `blockRank s : Fin (256^32)` through `ModuloCounting.reduce` to `Fin(P^8)`, then through `fieldRank`; `gammaNZ` uses `Fin(P^8-1)` and `nonzeroRank`, and `gamma` forgets the nonzero subtype ([`ModuloField.lean:76-84`](../../v8-r0-close-20261007/lean/R0C/ModuloField.lean)). `ordinary_mass_257` and `gamma_mass_257` give point-mass bounds `257/256^32` ([`ModuloField.lean:100-124`]); `gamma_ne_zero` follows by construction. These are exact finite maps for the *modulo-based* sampler model in `ModuloField`, not equalities to the current R1 transcript’s sampler call.

Likewise, old `R0P.SemSource.qm31Sample` is `qm31Rank (reduce (blockRank s))`, and `qm31Sample_mass` / `qm31Sample_mass_slack` bound this rejection-free modulo model ([`SemD2.lean:179-203`]); `semChal` embeds it into `WideExact` through `algebraMap` and `semChal_mass` preserves its pointwise bound using injectivity ([`SemD2.lean:205-223`). This is a QM31-valued model on the shared 32-byte state space. It is not a theorem that the current Rust `Transcript::challenge_qm31` returns that map.

There is older Aeneas sampler execution work: `R137SamplerInnerLoop.eight_attempts` and `source_result_invariant`, then `R169InnerSamplerExecution.eight_attempts_map`, establish bounded-loop execution facts. `R598NativeOrdinarySampler.challenge_map` relates the generated R569 and R156 versions of `challenge_qm31` (the R598 module imports the two snapshots and those execution modules). `R445InitialBlockRejectionLaw.initialBlockResult`, `initial_block_mean`, `initial_block_failure`, and `initial_block_value` model first acceptance from eight masked 31-bit words. `R601ExactFieldMass.source_independent_field_mass` gives the exact historical `challengeProgram` point mass for a QM31 value. These declarations are reusable execution/distribution results for their pinned historical translated sampler snapshots; they do not identify the current R1 `UnifiedSampler.samp` or current `Transcript::challenge_qm31` with those old sampler maps.

There is also a current-tree sampler-shaped arithmetic and byte-pass chain, which narrows the earlier gap. [`SamplerNatModel.qm31Digits_value`, `ordinaryDigits_value`, positional-rank corollaries, and `gammaDigits_value`](../lean/SamplerNatModel.lean#L41) prove that the four- and eight-M31-digit lists have values `x % P^4` and `x % P^8`, and that the explicit `endAround` list has value `x % (P^8-1)+1` for `x<2^256`. The adjacent bounds theorem gives a nonzero value below `P^8`. These use [`SamplerAddBridge.endAround_value`](../lean/SamplerAddBridge.lean#L35), whose list-add/carry implementation is related to modulo/division, and the quotient bound in [`SamplerMachineBounds`](../lean/SamplerMachineBounds.lean#L44).

The same current chain reaches decoded bytes for one arithmetic pass. [`SamplerByteWord.decodedArray_word_toNat`](../lean/SamplerByteWord.lean#L11) relates each Aeneas `U32.from_le_bytes` four-byte slice to `SamplerWords.word` for `SqueezeOracleBridge.decodeState`. [`SamplerBytePass.digits_values` and `machineProcess_bytes_correct`](../lean/SamplerBytePass.lean#L14) package the eight words in the reversed order used by the high-to-low pass and specialize the arithmetic result to the decoded 32-byte array. [`SamplerWord.machineStep_quotient_toNat` / `machineStep_remainder_toNat`](../lean/SamplerWord.lean#L99) and [`SamplerWordPass.machineProcess_correct`](../lean/SamplerWordPass.lean#L51) prove that bounded UInt64/UInt32 pass computes Nat quotient/remainder. `SamplerNatModel.radix32_pass` separately applies the generic long-division pass to `numeral B digits`; `SamplerMachineBounds` supplies the concrete `P=2^31-1`, `B=2^32` bounds. The focused evidence packages for NatModel, BytePass, ByteWord, WordPass, and MachineBounds are under [`evidence/`](../evidence/); they record green focused targets and their axiom reports.

### Selected 33-row model and checked mathematical bridges (2026-10-15)

The focused green modules now add checked model-level links, without closing the source-loop gap below. [`SelectedSamplerRanks.stateRank`](../lean/SelectedSamplerRanks.lean) is `R0C.ModuloField.blockRank` transported to `Fin (2^256)`; its `ordinary_eq`, `gamma_eq`, and `qm31_eq` identify the `OpeningSamplerBound.sample`/`gammaSample` and reduced QM31 rank maps with the old modulo maps. These are positional equalities over the shared Lean `State`, not Rust sampler refinement.

[`SelectedChallengeMap.sigma`](../lean/SelectedChallengeMap.lean) and its exported lemmas make the selected row map explicit: rows `<25` are `R0P.SemSource.semChal`; rows 25 and 26 retain that embedded semChal, and `rhoOf` projects it back to `qm31Sample`; row 27 is the existing gamma model; rows 28–30 are the ordinary model; row 31 is zero; row 32 is a reduced QM31 rank. `first_circle_view` and `second_circle_view` connect the two rho-derived parameter views to the existing `circleSample0` and `circleSample1`. The actual legacy namespace is `R0P.SemSource`, defined in the source file `R0P/SemD2.lean` (not `R0P.SemD2`).

[`SamplerRepeatedPass.run_digits`, `run_remaining`, `run_digits_value`, and `run_digits_canonical`](../lean/SamplerRepeatedPass.lean) compose the already checked abstract bounded word pass with the natural-number model: for supplied `UInt32` word lists, the remainder list is `lowDigits`, its value is the input word rank modulo `P^n`, the remaining word value is the quotient, and all digits are canonical. [`SamplerBlockRank.word_numeral_eq_rank`](../lean/SamplerBlockRank.lean) equates the reversed eight-word base-2^32 numeral to `R0C.ModuloField.blockRank`'s 32-byte positional value. This finite symbolic identity is not itself a proof that Rust's array/index loop supplies exactly that list to the repeated pass.

[`SelectedTranscriptParams.params`](../lean/SelectedTranscriptParams.lean) packages the chosen mathematical model with `L=131072`, `D=3717`, `iv=0`, `rounds=33`, labels `160+i`, and `σ=SelectedChallengeMap.sigma`. Its `Message` codec enforces only the 3717-byte bound; `publicStatement` requires a successful `SemanticPublicWire.parsePublic` result and assigns tag 2. The type is not row-specific message validity. The selected-challenge-map and repeated-pass bundles use source base `764bf20a6fe0392951b670f73748a54f70c9f272`; `SelectedTranscriptParams` also pins the direct imports `SelectedChallengeMap`, `UnifiedSampler`, and `SemanticPublicCodecComplete`. All four bundles' own READMEs and source manifests explicitly leave Rust refinement or full protocol/security closure out of scope.

The remaining interface gap is narrower than “sampler laws are absent”: the inspected declarations do not compose the eight repeated passes and their end-around update into one theorem from the exact 32-byte block rank (`blockRank`/current `decodeState`) to the returned four- or eight-limb tuple and then to the current R1 `Transcript::challenge_qm31`/`UnifiedSampler.Params.σ`. The older [`R406SamplerWordDistribution.word_value` and `words_value`](../../v8-full-view-zk-20260912/lean/AspisV8R19/R406SamplerWordDistribution.lean#L46) already connect each state’s four-byte groups to eight positional `Fin (2^32)` words and the split-block equivalence. But the current `SamplerBytePass.machineProcess_bytes_correct` is explicitly a *single* pass result and says it does not establish the sampler loop or `blockRank`; `SamplerNatModel` explicitly leaves fixed-width packing, field-tuple decoding, and Rust refinement outside its model. The older [`SamplerFieldDecode.decode4`/`decode`](../../v8-full-view-zk-20260912/lean/AspisV8R19/SamplerFieldDecode.lean#L12) is a reusable interpretation of four natural limbs as `QM31Exact` (and defaults on non-four-limb lists), but the inspected files do not connect it to a composed repeated-byte-pass result or to the current R1 transcript return value. The concrete remaining glue is therefore the flattened 32-byte/block-rank to eight-word numeral identity, iteration of the bounded pass across all eight source passes with the end-around state update, and composition of that result with the four/eight-limb field decoder and the current R1 sampler call. The reusable pieces support a selected-row sampler model, but do not by themselves prove current R1 source correspondence or instantiate the current adaptive sampler law.

In current R1 Lean, `UnifiedSampler.samp` is parameterized by generic `FS2.Duplex.Params`; rows 0, 26, 31, and 32 dispatch to the initial, reseeded, query, and plain sampler components, respectively ([`UnifiedSampler.lean:21-70, 77-106`](../lean/UnifiedSampler.lean)). `UnifiedSamplerLaw.unified_law` assumes `hD`, `hi31`, and `messageValid`, then states an `independentMean` equality in terms of the supplied abstract `p.σ i b` ([`UnifiedSamplerLaw.lean:21-54`](../lean/UnifiedSamplerLaw.lean)). It does not instantiate `State` as `Fin (2^256)`, choose a concrete state rank, or prove that the challenge map is `qm31Rank ∘ reduce ∘ blockRank`. `GammaSubfieldBound` imports the old modulo `gamma` model; it is not a sampler-refinement bridge for R1 ([`GammaSubfieldBound.lean:1-6, 37-73`](../lean/GammaSubfieldBound.lean)).

Current Rust source also exposes distinct functions: the R1 cost-probe `ordinary_sample` and `gamma_sample` are documented as modulo-ranked WideExact maps ([`sampler.rs:75-91`](../../../../crates/aspis-r1-cost-probe/src/sampler.rs)); the core transcript `challenge_qm31` instead reads little-endian words, masks by `P`, retries a limb when the masked word equals `P`, and returns an error on retry exhaustion ([`transcript.rs:395-431`](../../../../crates/aspis-core/src/transcript.rs)). The older finite modulo sampler theorems therefore cannot be cited as the source-level challenge sampler law without an additional refinement result. I found no current-tree Lean theorem connecting R1 `UnifiedSampler.samp`/`p.σ` to either the Rust rejection sampler or the old modulo-rank functions.

## Source pins

SHA-256 pins for the cited sources:

| Source | SHA-256 |
| --- | --- |
| `v8-r0-close-20261007/lean/R0C/ModuloField.lean` | `2c0f918c9eb6ac2ab93e07f955d3a5423a968dcefa01fcde58b31feb19d86594` |
| `v8-r0-close-20261007/lean/R0C/ModuloCounting.lean` | `78bb90fb18ed67ce8d51c4318b28044815e2ba21dd3d81ecc165515c30686972` |
| `v8-r0-close-20261007/lean/R0C/ConcreteSlack.lean` | `a716935c3d2ab4cb782e1b2b1e591f43e95db60f68b231c691a89a922a318a19` |
| `v8-r0-sem-proof-20261008/lean/R0P/SemD2.lean` | `2b68437dfd6ba62cd023013a5b514987255550124c0eca4abb03a26a560397c0` |
| `v8-full-view-zk-20260912/lean/AspisV8R15/ExactTowerBase.lean` | `04cc89947881df177c331450193641af3024ccfd00d3e836112017625517ffd5` |
| `v8-full-view-zk-20260912/lean/AspisV8R15/ExactTowerFinite.lean` | `13f8aa89fbe0489f9fccaa58023fd858ca72897726cdeeebcb60048610ea175c` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/R599CanonicalFieldTuple.lean` | `eb4d5dfb9c8bc42f5a0086ff203291a592d7f67bc01990de489862fb4dc242a5` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/SourceDuplexStep.lean` | `1c22a3c25b03f0b83fb7b245e618fa2e9f62c7c7bc1d1bd9de14f5c5f0f5665f` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/UniformStateFirstHit.lean` | `f92fa3c19fc609cc25d228b7bec947678a1bfcccc81434adfa758d73865eda01` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/R406SamplerWordDistribution.lean` | `b7b3aa0f3f42e39ce5945f3d4bdaad7544f2dfd39292ecf0bc26b9ea9eac1ed9` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/R445InitialBlockRejectionLaw.lean` | `efe55338ba9bc5a7ccf7c0383a431e1922ebaf80b7931b2798025eb8f4750d81` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/R137SamplerInnerLoop.lean` | `146a6e0970f3b649eb9a9321b411808e3222521ba4065af11f120d29e9421a29` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/R169InnerSamplerExecution.lean` | `f8eeffa227bf0afa2544f8e9b424cb6d8ac1e5768ccfecef215d1976b7515067` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/R167TranscriptPrimitiveExecution.lean` | `3d4c55d2b8c9e542d71daa795929c3100cede9784d2c7497cdc2a43734480325` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/R577NativeInnerSamplerExecution.lean` | `28642fca8289dbc82eb2f4ff30142f201bdd711154d63114f7933ed13ff56efb` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/R584IndependentBlockSampler.lean` | `8c412bfcc92c734de86531a8f9b46950ac5d7b13f71731adbdb0cae9d0f5e56f` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/R580SourceWordStream.lean` | `297538faee8ac73ad4fe367e36ebf31e3938599dfa2eb371f2c82cb7d135e029` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/R572SequentialWordMass.lean` | `cb40bdb40b9ebd4a15ca7c8f96c8e114f9f5e2dd11cf730dfd32986696f12e46` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/R589IndexedReplyExecution.lean` | `4f1a8a42443ac1fd3bdc00bcfdb0bbc8f4b2cd9d416aecfd11214d974abe6c6d` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/R592FiniteBlockExecution.lean` | `1a66becfca17d199af96be1b41f58ffe45de8fb7f5d336b3b98f9faae951d74e` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/R594JointChallengeMass.lean` | `e67591dce5709988ff99671d1ce157e8d9db5ec85a9de53b9bb31bf31055f5c8` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/R601ExactFieldMass.lean` | `419f27cd81bdf57724fb66282643ddb5e5299e0aa92592da9ac4cb09b6746255` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/R598NativeOrdinarySampler.lean` | `9f0be3389c15c5ceda803a4ed766ac29ace8bfedf489931de062857dff982eca` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/SamplerWordBridge.lean` | `f15b082b888ac9c0fddc08d00a6345a33f4cd6aa863fe5e43bd5a1f04930171f` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/SqueezeOracleBridge.lean` | `0c31a94042e6834ddfce790e049a247081590c1ddafec324faaa3f397cd01531` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/SamplerWords.lean` | `21f5742355920ce7f6a70496e6255e8d50d10739a75b8a5671030eea6fb1dbb9` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/SamplerWordRead.lean` | `bb8ec7e56a78fea545f582b0fe930525a994d887b4d9dd03d7488b6ad42dc49d` |
| `v8-full-view-zk-20260912/lean/AspisV8R19/SamplerFieldDecode.lean` | `188a787cfd90d5458bdfddf90bb8ce28dfb52e2ae6fc3b2abafe28aad97ad10b` |
| `100bit-spend-path-20261013/lean/SamplerRanking.lean` | `f41de78e7b64f737df7b86346f2f39972a0165fdf275ced4957b6a6372395b4b` |
| `100bit-spend-path-20261013/lean/SamplerNatModel.lean` | `e2041176802dd226819b72c83ad311c601986ebfb37ce5544402d55be68463e6` |
| `100bit-spend-path-20261013/lean/SamplerBytePass.lean` | `31a64db268f34228105a160ce96d525060d31b22c19722ab7581a8d533feadbc` |
| `100bit-spend-path-20261013/lean/SamplerByteWord.lean` | `ee86df7c9c2cb4ca0db1965c210a2f495ddd40377f215215b6addcadb6a2c521` |
| `100bit-spend-path-20261013/lean/SamplerWordPass.lean` | `16f37454a6d5e3672ee0f3a5c6c195926c3d9e64c4d7d423b79d1eabd87d6b11` |
| `100bit-spend-path-20261013/lean/SamplerMachineBounds.lean` | `cb1d5e53fa26c968d16d84f4011747842c41d6a05c24bece76319f00023f54cd` |
| `100bit-spend-path-20261013/lean/SamplerWord.lean` | `8206a4a664485894d4e3aff5443acfcff389445fb4e4c341269a9fd2aa440598` |
| `100bit-spend-path-20261013/lean/SamplerPass.lean` | `631e025882495fcc5b2a402b9b002edc594080269c37553fd165499e61b9e0dd` |
| `100bit-spend-path-20261013/lean/SamplerLongDivision.lean` | `6b0a35daf77c00c8cb45fe627b0e4fbdf07f50da714a3737dc045939f790ed8c` |
| `100bit-spend-path-20261013/lean/SamplerAddBridge.lean` | `22a9d1474abe3ebbefaae867a287f15e36c572a2d51ff9b846f5478c713496a8` |
| `100bit-spend-path-20261013/lean/SamplerArithmetic.lean` | `fc7502a6119f5626e2391c6592c4127b1bd5af073a5b4e07afdc7cab1c8cccec` |
| `100bit-spend-path-20261013/lean/SamplerAddDigits.lean` | `174cca73fae636a113242c08f938d451a1234ba237dddfeb3da78afb2ad02b62` |
| `100bit-spend-path-20261013/lean/SamplerCarry.lean` | `cb56f879bd84899100f3755d6cb43db8aa333da3ae9944956118c1713fd913d8` |
| `100bit-spend-path-20261013/lean/SamplerDigits.lean` | `63f68242e997faf598724e969130acd60085382c673c60d2819cbfbc19b67ed9` |
| `100bit-spend-path-20261013/lean/UnifiedSampler.lean` | `ac0ed518595233c81a4b2c3f368bb20c513cb29b888f19dc586801a9ac0b98ad` |
| `100bit-spend-path-20261013/lean/UnifiedSamplerLaw.lean` | `48b24649ed6bca0e21fcd0c4a9418cb1d4c8baae74db542e26e8a25f0781e910` |
| `100bit-spend-path-20261013/lean/GammaSubfieldBound.lean` | `2dd2b78cfd584050c37aced3298ffc18cce3377ae2f428055578ea5fdcc31c0e` |
| `crates/aspis-r1-cost-probe/src/sampler.rs` | `be426dfc4049682ef2d90940ee42bf9cffbec2db1d2d9b965e9c14e491948b8c` |
| `crates/aspis-core/src/transcript.rs` | `9bd74c66a28567e4d964896b7e2d7c0ac79840565d44b561747879868bdd9179` |

### Added 2026-10-15 source pins for selected model

| Source | SHA-256 |
| --- | --- |
| `100bit-spend-path-20261013/lean/SelectedSamplerRanks.lean` | `5e80166fd121340b45df200ee9b14b51e83895ff8382a2e95a59f9f793d1bf11` |
| `100bit-spend-path-20261013/lean/SelectedChallengeMap.lean` | `36bcd2bb277dcb2b34564656c71ebb7b14742c584ce931328a2ad1dbe03e5aad` |
| `100bit-spend-path-20261013/lean/SelectedTranscriptParams.lean` | `489f8b49c6a102f85c511ad4f4907dbeca479322b7184a563eda8c4a17c2dce0` |
| `100bit-spend-path-20261013/lean/SamplerRepeatedPass.lean` | `4e410be230bc6cd19147d3b3e0e4f2eb2330b4e504ea1735668baaf05dbd8424` |
| `100bit-spend-path-20261013/lean/SamplerBlockRank.lean` | `53c026effac66b2222dfe3d6a2e39035f0bccf5fa4d059e583a9938daaf8d632` |
| `100bit-spend-path-20261013/lean/SamplerNatModel.lean` | `e2041176802dd226819b72c83ad311c601986ebfb37ce5544402d55be68463e6` |
| `100bit-spend-path-20261013/lean/SamplerWordPass.lean` | `16f37454a6d5e3672ee0f3a5c6c195926c3d9e64c4d7d423b79d1eabd87d6b11` |
| `100bit-spend-path-20261013/lean/UnifiedSampler.lean` | `ac0ed518595233c81a4b2c3f368bb20c513cb29b888f19dc586801a9ac0b98ad` |
| `100bit-spend-path-20261013/lean/SemanticPublicCodecComplete.lean` | `f7dbf21c91fabf47e21a7d835b45f8211b489061576fb38f5a485e514a154000` |
