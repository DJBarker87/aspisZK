# Causal first-hit reuse inventory

Source inventory at worktree HEAD `ce1fb7255213f5b390048d1ca709fea99176ae62`. This records existing theorem interfaces and conditional adapters; it does not prove a current R1 classifier, acceptance-to-hit implication, or security bound. One focused adapter target was subsequently compiled; its full receipt and attempt evidence is under `evidence/lean-unified-causal-bound-20261015/`.

## Direct first-read bound

`FS.LemmaA` is the closest generic theorem for a causal predicate `bad : Addr → Table Addr State → State → Prop`. Its specification is `FS.LemmaA` in `docs/research/v8-fs-generic-20261006/lean/FS/Statement.lean:270-281`; the checked implementation is `FS.lemmaA` in `FS/LemmaA.lean:121-122`. Given `0 ≤ ε`, a pointwise bound

```lean
∀ a T, mean (fun answer => indicator (bad a T answer)) ≤ ε
```

and `FirstReadsBound q t N`, it proves

```lean
lazyMean q t (fun v => indicator (hitsBad bad t v.1)) ≤ N * ε.
```

`hitsBad` checks `t a = none` before applying `bad a t answer` (`FS/Statement.lean:55-57`), so `T` is the table immediately before a first read. To apply this to an oracle experiment, the exact program needs a `FirstReadsBound`, obtainable from a pathwise `firstReads`/`distinctFirstReads` cap through `FS.firstReadsBound_of_traces` (`FS/Theorem.lean:115-118`), plus the existing empty-oracle/lazy-mean experiment conversion.

This is a density-to-hit theorem only. It does not prove the pointwise density premise, identify `bad` with a decoded R1 row, or show verifier acceptance implies a hit or extraction.

## Related union and decoded-chain interfaces

`AspisV8R19.CausalFirstHitUnionBound.mean_firstHit_union_le` (`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/CausalFirstHitUnionBound.lean:48-65`) takes `bad : I → X → Prop` and a full-sample mean bound for every index; it concludes the bound for the union over indices. It does not express a table-conditioned fresh-answer premise. `CausalTapeFirstHit.mean_causal_firstHit_le` (`.../CausalTapeFirstHit.lean:65-73`) instead takes `bad i history current` and a fresh-current-answer bound for every history, on a finite product tape. It still needs a bridge from an adaptive oracle trace to that tape model.

`FS2.LemmaA` (`docs/research/v8-fs-generic-20261006/lean/FS2/Statement.lean:275-285`, implementation `FS2/LemmaA.lean:245+`) is the sampler-valued decoded-row analogue. For each address/table and each decoded `Sampler S`, it requires a bound on `independentMean S.toProgram` for `bad prefix message table challenge`, plus `FirstReadsBound`; it bounds `hitsChain` by `N*ε`. It does not require RoundByRound, D1, D2, or D3, but its decoder field must return that sampler.

The older V3 interface is `R0C.V3.ChainDensity3` (`docs/research/v8-r0-close-20261007/lean/R0C/V3/Gen.lean:38-42`). For every decoded `(own, pend, g)`, its premise is the whole law `blaw g (fun out => indicator (d2Bad pr rb out.1 out.2.1 T out.2.2)) own pend ≤ maxErr rb.ε pr.r`. `R0C.V3.theorem43` (`Gen.lean:251-257`) additionally requires D1, D3, `ChainsRead`, `ReadsChains`, an `Inj3` package, and the distinct-first-read bound.

Crucially, `R0C.V3.lemmaA3` (`Gen.lean:64-67`, proof uses `blaw` at `:80-110`) already is the arbitrary-background first-hit theorem. It accepts an independent `Dec` returning `BS`-style `(own, pend, g)`, an arbitrary `bad`, a nonnegative ε, a per-decoded-output `blaw` density premise, and `FirstReadsBound`; it concludes the `N * ε` bound for `hitsChain3`. It requires none of D1/D2/D3. The compiled R1 adapter in `lean/UnifiedCausalBound.lean` proves `first_hit_bound`: a uniform row/prefix `independentMean` bound is transferred by `UnifiedDecoderBound.decoded_bound` to each decoded `blaw`, then passed to `lemmaA3`. Its companion `empty_oracle_first_hit_bound` replaces the pathwise `FirstReadsBound` input by a `distinctFirstReads` cap using the existing trace bridge and empty-oracle law. These are conditional density-to-hit results; neither supplies the uniform row-density premise nor acceptance-to-hit/extraction. Exact source/object, axioms, capped receipt, and all three source snapshots are recorded in `evidence/lean-unified-causal-bound-20261015/`.

`UnifiedChainDensity.chainDensity` (`lean/UnifiedChainDensity.lean:23-64`) is a different adapter: it derives V3 `ChainDensity3` from `FS2.D2` and `UnifiedDecoderBound.decoded_bound`. That route remains available for `theorem43`, but is not required for the direct `lemmaA3` first-hit route above. `UnifiedProtocol.protocol.decode` remains `none` (`lean/UnifiedProtocol.lean:24-32`), so the sampler-valued `FS2.LemmaA` does not directly describe the R1 background decoder. The separate V3 `Dec` interface does.

Current `UnifiedProtocol.protocol` deliberately sets `decode := fun _ _ => none` (`lean/UnifiedProtocol.lean:24-32`). `UnifiedDecoderBound.component_bound` and `.decoded_bound` (`lean/UnifiedDecoderBound.lean:26-38,186-199`) only transfer a supplied uniform bound for every row and fixed prefix length to a `blaw` for the decoded background sampler. They do not prove the density premise for a first-read predicate and do not adapt the `List State` background sampler into an `FS2.Sampler` for `FS2.LemmaA`.

`UnifiedOracleInj.inj` (`lean/UnifiedOracleInj.lean:18-53`) packages the existing `Inj3` interface, with public-byte bound, all-row label equality, initial-record encoding, total first-read cap, and a combined collision event. Outside that event it uses `UnifiedOracleTotalCase.decodes_and_follows` to obtain the current decoder output at the first-read table and its completed row output. This supplies decode/follow facts, not an acceptance-implies-causal-hit theorem.

## Table-to-final word stability

`FirstReadCut.tableBefore_representation` (`lean/FirstReadCut.lean:34-42`) decomposes a trace at the first occurrence of an address and equates the table there to replay of the preceding records. `CanonicalTableRecovery.represented_before_cut` (`lean/CanonicalTableRecovery.lean:40-62`) equates recovery from that pre-cut/represented record list when replay equals the cut table. Its premises include full-trace oracle consistency and query cap, a no-duplex-collision event exclusion, and first-occurrence/replay facts.

`CanonicalRecoveryStability.recover_stable` (`lean/CanonicalRecoveryStability.lean:77-103`) compares recovery from `pre` with recovery from `pre ++ post` for a fixed commitment root. It requires consistent answers, a query cap, no duplex-collision, no child-target hit, no selected-root prediction hit, and a commitment read in `pre` whose parsed predictor identifies that root. Root-specific wrappers are `C1TableStability.c1_table_word_of_read` (`lean/C1TableStability.lean:72-112`) and `LaterTableStability.c2_table_word_of_read` / `.folded_table_word_of_read` (`lean/LaterTableStability.lean:18-67,69-123`). These can support a first-read-table versus final-recovery equality after their explicit premises are established; they do not supply those event exclusions.

## Density premise still open

The remaining density obligation is to establish `hfixed` for the chosen decoded-row bad predicate. The initial law (`UnifiedInitialLaw.sampler_law`) samples multiple answers, row 26's reseed law (`UnifiedReseedLaw.background_sampler_law`) includes an additional reseed answer, and the query law (`UnifiedQueryLaw.background_sampler_law`) samples a sequence of addresses/states. `UnifiedDecoderBound` preserves those whole-component laws, and `UnifiedCausalBound` consumes the resulting uniform `independentMean` premise per row and fixed prefix. No component-specific bad-event density bound is established by these generic adapters.

The rowwise uniform density premise needed by `UnifiedCausalBound` remains unproved. Applying `FS2.LemmaA` directly would additionally require a sampler-valued `Protocol.decode` interface; the direct R1 theorem instead uses V3 `lemmaA3`, whose decoded law already accepts the multi-answer background sampler. The separate collision term is available from `CombinedMerkleCollision.mass` (`lean/CombinedMerkleCollision.lean:116-141`) under the full distinct-first-read bound.

## Source pins

| Source | SHA-256 |
|---|---|
| `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/CausalFirstHitUnionBound.lean` | `b8fcef9a70134fdb5d60dbf127a0f1f6ed85dc9e9484781f2de4b71324c29f38` |
| `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/CausalTapeFirstHit.lean` | `a4276c264eaa3180a6a7a617a5cf8252a2f6232bf703522e2d85bb8897988659` |
| `docs/research/v8-fs-generic-20261006/lean/FS/Statement.lean` | `7251b37e0302e26dd40bd05cc60665c884b5899e1e96e3b5c9402404b2e6bd78` |
| `docs/research/v8-fs-generic-20261006/lean/FS/LemmaA.lean` | `fbae67b310e92c85afee01803f7b8cda01181f8190b001e5ef91453ad08650bb` |
| `docs/research/v8-fs-generic-20261006/lean/FS2/Statement.lean` | `e472de7d36479495d55e10436635344bf7d2187f223ae73bd0b1db3c78718b36` |
| `docs/research/v8-fs-generic-20261006/lean/FS2/LemmaA.lean` | `bc20b02b6cf5b5506acc3887ccd83e571cbcf2934220675fc13bd126275fad03` |
| `lean/UnifiedProtocol.lean` | `0087deb2a71b080806da8601bf469d623e06a4e83692cbf943339768f28ecb45` |
| `lean/UnifiedDecoderBound.lean` | `a909cbb8259c00b839f13f8248f7fd8b2c6411647c97ff936f0c57145d235c3e` |
| `lean/UnifiedOracleInj.lean` | `bff4eec1d5c0e7916f812f76173aa4f0880965e94c010db5ce54d47cdce94bef` |
| `lean/UnifiedOracleTotalCase.lean` | `7c813d83bb399fe643c0fedd8f26b7ea10c75a72da078a778f94e31da75ff350` |
| `lean/FirstReadCut.lean` | `ba8b98c84f9d9168850005fab77dd656a525dbf0ed52781ca97620055943a31e` |
| `lean/CanonicalTableRecovery.lean` | `7e62ac6515d0a21addbbf213323e80a6265e8747e4a6a61e89174ffea0e3e5ee` |
| `lean/CanonicalRecoveryStability.lean` | `1c3087658c794a0cec4fe8ae738281988a8d0da893f6230669f90882f4897545` |
| `lean/C1TableStability.lean` | `be8c0856d229f363a852922af3394841bfcbb19e289c08e6a4f4436ba9b8e36f` |
| `lean/LaterTableStability.lean` | `122945807038764795c933eef9b779151d2d725f701375644bce56fbf61050c1` |
| `lean/CombinedMerkleCollision.lean` | `91484974934eeb3dc9506a992e73e08207404fada9cc6348f74028c0d218e5a6` |
| `docs/research/v8-r0-close-20261007/lean/R0C/V3/Gen.lean` | `0a6aff242cde2900929ccc098322ecf06911747781d444fd0b0f41750101691f` |
| `lean/UnifiedChainDensity.lean` | `0b17f5e0f0fb348f6717cb9891a139ae90326bd88b6bd9e2cbca84ca354000d1` |
| `lean/UnifiedCausalBound.lean` | `310c167bc6f212dc5feb94d9c5d0768cbfecfe8ade549ddf8f6c2331d4d532f8` |
