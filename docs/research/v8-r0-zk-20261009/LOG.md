# Z1 — R0 interactive privacy statement skeleton (2026-10-09)

## Scope and pins

Read-only Phase 0 started in `/Users/dominic/ZK` (main `acd4c0f0d0049d42c9fcb9525900fbb8932f1baf`); the requested sources live in `.worktrees/ZK-v8-r21-public-arithmetic-20260922`, branch `research/v8-wide-reference-20261005`. This job writes only the new `docs/research/v8-r0-zk-20261009/` directory. Existing soundness edits and all old privacy files are left untouched. No Aeneas continuation, Rust build, finite-field enumeration, or wallet/key operation.

Phase 0 citations are relative to that worktree at **`ab6bbce28a64f8d208c49097ea64713af711321f`**, the revision observed on entry. Citations include line numbers and refer to git objects at this pin, not an unlabelled mixture of evolving worktree files. The lead's G22 edits were already in progress; the final skeleton does not select a circle policy. The requested soundness LOG was read from “Lead: D3 core” through G20 and the G22 obstruction/interface decision, including subsequent live continuation entries. The G20 theorem is a soundness result under the recorded model decoder identities, not a privacy result or a frozen Rust refinement.

The old privacy SOURCE_MANIFEST pins a different historical generated target (`9e432896a4e1515efebe940b71fd9b4f9f009189`) and explicitly leaves generated closure/source adapter authentication open (SOURCE_MANIFEST.json:4–5, 16–26, 27–52). That git object is unavailable in this clone. The old documents are evidence of the stated experiment/ledger and diagnostics; the Rust audit below is expressly at the available pin above. It does not authenticate the missing generated deployment closure.

### Source hash inventory

| Pinned source | SHA-256 | Matches worktree at inventory |
|---|---|---|
| `docs/research/v8-full-view-zk-20260912/PRIVACY_LEDGER.md` | `28ad81a71e8c461b56a360b418393bbaecd6e0479a7027efac3c2b423540c5e2` | yes |
| `docs/research/v8-full-view-zk-20260912/HONEST_PROVER_EXPERIMENT.md` | `6ee4c1f993fc3af27acc3ef29d02e105ce0578be28d0ac549be02e77e44558c0` | yes |
| `docs/research/v8-full-view-zk-20260912/PUBLIC_VIEW.md` | `bc73437a2ae0348dc8e37160516f190d9870cecbc1e45483200fbde313288809` | yes |
| `docs/research/v8-full-view-zk-20260912/CURRENT_STATUS.md` | `15e149419622799dbd7bce41c2074082740411b1e87c2dfd50caa5c6c78fac96` | yes |
| `docs/research/v8-full-view-zk-20260912/VALID_PAYMENT_QUANTITY.md` | `c315f76028b772150bdb45d3b402da902f945ce53c220b93190d0e0ef170f2e1` | yes |
| `crates/aspis-prover/src/state_only_entropy.rs` | `78ebbb3176daf23935243452992548ff9d877aaaf853d73e5ee46b60d8cb3ec0` | yes |
| `crates/aspis-prover/src/state_only_hiding.rs` | `48dddafce0ea55d5df2f6b670cd8c571cd182e446ce34ea8b3d42aa313b32d3f` | yes |
| `crates/aspis-prover/src/state_only_candidate_prefix.rs` | `3095f73ca6d54b633cd8d4ba8029e9a0f34136a6d2828410476c0b60fc8c29ab` | yes |
| `crates/aspis-prover/src/v6_onefold_prover.rs` | `1715970722d3e183771ff41711a760578deac0522038a3a7d2dd519f90c9a433` | yes |
| `crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs` | `61bcd59a22c9c02fe3f9ba69cda43bfa8fe02ea14f15da9b761e976fe48798bf` | yes |
| `crates/aspis-statement/src/state_only_terminal.rs` | `1e4ae2058a92c0c8fb6217144ac0c092e233ab4dd8f4e63a85cdab7b2ae121a5` | yes |
| `crates/aspis-core/src/transcript.rs` | `be036d144b9fe0c8119d9f6fdd8ca2167d1379f7d1d785fa2f197200b9f7d119` | yes |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemView.lean` | `01868627189632007beaac02e9036d71d4f268dfe9c3f4d8b51ee9964de528e1` | yes |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemDecision.lean` | `cf8c98e1bf6d5da3a2e725efd3790c4efc7e75fc32b0c650c310d875bf1f8971` | yes |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD3Glue.lean` | `26f6c39987de422e0b38779db55e8c26ce728d4c6a01a9061ff9f4157b16bf17` | changed concurrently; citations below use git object |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD2.lean` | `ef7b48c25eefa272398f78472ecbcbc9f5221a8465ef2f414cf711ba79af99d9` | yes |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/Core.lean` | `eba6bb784803b5f00922724efc9997a8d5ab6bc55cd8c100bffd8a397dabe1f9` | yes |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/Semantics.lean` | `9309c5faa3de30d4f35bfe46509fe335a821d89a43051201a97232c0b89dc615` | yes |

## Phase 0.1 — honest experiment, entropy, public outputs, ledger

Citation abbreviations: **P** = `docs/research/v8-full-view-zk-20260912/`; **S** = `docs/research/v8-r0-sem-proof-20261008/lean/R0P/`; **C** = `docs/research/v8-r0-close-20261007/lean/R0C/`; **O** = `docs/research/v8-r0-fs-20261006/lean/R0FS/`. These are the pinned sources above unless explicitly marked live. Historical fixture/positive-q22 claims are not silently promoted to the R0 model.

### Randomness inventory

| Source of randomness or derived random material | Source and scope |
|---|---|
| Two private 32-byte seeds: field-mask entropy and leaf-salt seed | P/HONEST_PROVER_EXPERIMENT.md:17–29; P/PRIVACY_LEDGER.md:19–25. `crates/aspis-prover/src/state_only_entropy.rs:202–224` obtains 64 OS-random bytes, retries all-zero private components and can fail. These seeds are not a statistically uniform tape of all mask coordinates. |
| Public attempt/mask nonce | P/HONEST_PROVER_EXPERIMENT.md:18–27, P/PUBLIC_VIEW.md:23–25. Preselected proof-account public key, reserved durably before derivation. Not a third private seed. The alternate 96-byte `generate()` API is expressly outside this adapter (experiment:22–24; entropy.rs:172–196). Account-key generation is environment setup, not silently additional prover entropy. |
| C1 relation-free M31 masks; ten full-domain M31 mask-only columns; QM31 G; QM31 inactive H1 padding | P/HONEST_PROVER_EXPERIMENT.md:28–29 and P/PRIVACY_LEDGER.md:19–23; exact expansion in `crates/aspis-prover/src/state_only_hiding.rs:388–402,429–480,619–643`. All derive from field entropy through domain-separated hash expansion. Balancing makes the resulting coordinates dependent. |
| D lane | Experiment:28–29; `state_only_entropy.rs:426–431,634–674,703–715`: a domain-separated derivation from the same field source seed, 1024 QM31 values with an inactive-sum constraint. It is not a third independent seed. |
| One private per-index 32-byte leaf salt, shared by the C1 and C2 trees | Experiment:28–29; ledger:24–28; public view:10–12,39–41. `state_only_entropy.rs:568–585` binds salt seed, attempt binding, nonce, tree-domain tag and leaf index. Same salt-derivation routine and index are used for both trees in `v6_onefold_prover.rs:995–1022`; the commitment leaf hashes still have separate C1/C2 tags. |
| Scalar challenge draws and bounded limb rejections | Public view:45–50; `crates/aspis-core/src/transcript.rs:378–415`. Derived from transcript squeeze blocks; in the old ROM experiment they use the one shared full-256-bit oracle (experiment:34–37), not independent OS randomness on each call. |
| OOD parameter retries and distinct-second-point retries | Public view:48; ledger:40–42; CURRENT_STATUS.md:54–90,141–150 records the fixed-tape/freshness boundary. `transcript.rs:453–465` implements bounded parameter retries. Failures/state advances stay in the unconditioned experiment. The R0 one-block circle model is separate; see Phase 0.2. |
| q22 draws, duplicate rejection / bounded exhaustion | Public view:50–53; ledger:40–42; CURRENT_STATUS.md:141–150. Model: C/V3/DuplexQ.lean:12–18,41–58 and C/V3/Q22Law.lean:89–96: eight squeeze/advance pairs, first accepted 22-fibre set, failure represented by the empty set. These are oracle/verifier randomness, not extra private seeds. |
| Retried proof attempts and public lifecycle | Experiment:25–33,44–56; ledger:46–61. Fresh reservation/secrets per permitted retry; do not assume IID attempts, grant grinding credit, condition on success, or erase terminal exhaustion. There is no additional independent “retry randomness” beyond the indexed entropy/oracle tapes. |
| Witness note salts / keys / path / amounts | VALID_PAYMENT_QUANTITY.md:24–34,38–53 and S/Semantics.lean:73–80. These belong to the fixed witness or prior application setup; they are not re-randomized honest-proof coins when quantifying over a given valid witness. |

The older top status entries expressly do not close the source or distribution boundary: P/CURRENT_STATUS.md:3–13 (R137),15–23 (R136),25–41 (R135/R134),43–72 (R133–R131). No Aeneas claim is imported as a privacy theorem.

### Full public output inventory

| Output / leakage | Citation |
|---|---|
| Full statement, proposed afterstate, allowed application outputs, profile/release identifiers | P/HONEST_PROVER_EXPERIMENT.md:10–13; P/PUBLIC_VIEW.md:7–9. Model `Public` contains variant, anchor, nullifier, assetId, optional recipient, change, optional withdrawal amount, nextPairIndex, snapshotFrontier, nextRoot and nextFrontier (S/Core.lean:55–67). |
| Output commitments, nullifiers, all roots and identifiers | Experiment:10–13; public view:7–12; model Core:58–67. Neither private transfer amounts nor the witness are automatically allowed leakage. |
| Proof/account framing, payer/account identities, public attempt identifier / nonce | Public view:7–9,23–25; experiment:18–27,49–56. Exact generated application-envelope location remains unauthenticated. |
| All serialized proof bytes and their lengths | Public view:10–12,27–41: 697 QM31 fields partitioned as initial mask claim 1, semantic rounds 270, point rows 87, inactive sum 1, two OOD vectors 58, relation rounds 24, final coefficients 256; C1/C2 roots; research nonces; 22 paired openings with one shared salt each; both authentication frontiers. Roots 26 bytes, each record 621 bytes (403 C1 + 186 C2 + 32 salt), each frontier at most 296×26 bytes, maximum body 40,282 bytes. These sizes are historical positive-q22 serialization facts, not an R0 serialization theorem. |
| Every message, challenge, and publicly reconstructible transcript value | Public view:13; model schedule below. Include the last prover message after challenge 30; it is not a 32nd challenge round. |
| Observer's own adaptive oracle queries and complete 256-bit answers | Public view:14; experiment:34–37. The 208-bit commitment projection does not create a second independent oracle. This is an FS/ROM-view field, outside interactive HVZK. |
| Publication/setup/account events, visible retry/attempt counts, success or opaque abort/exhaustion | Public view:15; ledger:40–51; experiment:30–33,49–56. Keep every event actually exposed; do not expose private rank/selector/entropy-error diagnostics merely because the prover computes them. |
| Explicitly not direct fields: private seeds, undisclosed tables/masks, private hash inputs, complete honest-prover internal oracle log | Public view:17–21. Indirect leakage through outputs remains part of the obligation. |

### Every ledger term (none assigned a value here)

The reserved one-session expression is `epsilon_seed + epsilon_salt + epsilon_commit + epsilon_algebraic_bad + epsilon_fs_conflict + epsilon_sampler_abort + epsilon_source` (P/PRIVACY_LEDGER.md:11–15).

| Term | Meaning | Source |
|---|---|---|
| `epsilon_seed` | Computational/ROM replacement or forbidden-query loss for the two private seeds versus ideal field/salt tapes; not statistical uniformity of 25,436 M31 coordinates | ledger:19–23 |
| `epsilon_salt` | Salt expansion failure / forbidden query, preserving one salt per leaf shared by both trees | ledger:24–25 |
| `epsilon_commit` | Lazy commitment/opening programming conflict in one 256-bit table with the exact 208-bit root/frontier projection | ledger:26–28 |
| `epsilon_algebraic_bad` | Conditioned allowed-witness displacement outside the remaining mask image; raw universal rank does not discharge it | ledger:29–36 |
| `epsilon_fs_conflict` | An adaptive prior query fixed the answer the simulator would need to program; distinguish agreeing cache hits and conflicts, never overwrite | ledger:37–39 |
| `epsilon_sampler_abort` | First-hit exhaustion, duplicate/distinct OOD failure, q22 failure, singular helper/denominator events, every visible proof-generation abort | ledger:40–42 |
| `epsilon_source` | Exact generated prover / serializer / application projection versus mathematical game mismatch | ledger:43–44 |

Also retained, without instantiation: conditional coupled-step losses `delta_i`, a conditional release lower bound `a > 0`, proposed retry totals `sum delta_i` and `(1-a)^K` (ledger:46–51); ideal-word mask-limb exhaustion `25471 / 2^496`, only a component of sampler-abort (53–55); adaptive-session hybrid/union accounting with query bounds, reservations, evolving public state and one oracle, no independence/multiplication assumption (57–61). The old R5 fail-closed boundary's release probability 0 and exhaustion probability 1 is a containment/liveness observation, not epsilon_zk=0 (5–9).

## Phase 0.2 — exact model transcript boundary

S/SemView.lean:30–34 defines `SemMsg.none`, `.h1 h g` carrying two `InitialWord K`s, and `.roundPoly p`. C/SemStatement.lean:18–33 defines outer `Msg` (`semantic`, `beforeZ0`, `beforeZ1`, `opening`) and `Chal` (`semantic`, `circle`, `opening`). S/SemDecision.lean:82–109 fixes scalar index use and semantic polynomial parsing. O/Protocol.lean:50–60,101–111,127–135 fixes opening messages/challenges and the terminal opening tag.

| Global round (zero based) | Prover message before challenge | Challenge value |
|---:|---|---|
| 0 | `.semantic .none`; context W already fixed | `.semantic λ` |
| 1 | `.semantic .none` | `.semantic χ` |
| 2 | `.semantic (.h1 h g)` — C2 words chosen after λ, χ | `.semantic θ` |
| 3 | `.semantic .none` | `.semantic zc₀` |
| 4 | `.semantic .none` | `.semantic zc₁` |
| 5 | `.semantic .none` | `.semantic zc₂` |
| 6 | `.semantic .none` | `.semantic zc₃` |
| 7 | `.semantic .none` | `.semantic zc₄` |
| 8 | `.semantic .none` | `.semantic zc₅` |
| 9 | `.semantic .none` | `.semantic zc₆` |
| 10 | `.semantic .none` | `.semantic zc₇` |
| 11 | `.semantic .none` | `.semantic zc₈` |
| 12 | `.semantic .none` | `.semantic zc₉` |
| 13 | `.semantic .none` | `.semantic μ` |
| 14 | `.semantic (.roundPoly p₀)` | `.semantic α₀` |
| 15 | `.semantic (.roundPoly p₁)` | `.semantic α₁` |
| 16 | `.semantic (.roundPoly p₂)` | `.semantic α₂` |
| 17 | `.semantic (.roundPoly p₃)` | `.semantic α₃` |
| 18 | `.semantic (.roundPoly p₄)` | `.semantic α₄` |
| 19 | `.semantic (.roundPoly p₅)` | `.semantic α₅` |
| 20 | `.semantic (.roundPoly p₆)` | `.semantic α₆` |
| 21 | `.semantic (.roundPoly p₇)` | `.semantic α₇` |
| 22 | `.semantic (.roundPoly p₈)` | `.semantic α₈` |
| 23 | `.semantic (.roundPoly p₉)` | `.semantic α₉` |
| 24 | `.beforeZ0 y`, `y : Fin 3 → Fin 29 → K` | `.circle z₀` |
| 25 | `.beforeZ1 y₀`, `y₀ : Fin 29 → K` | `.circle z₁` |
| 26 | `.opening (.values yOOD)`, `Fin 29 → Fin 2 → K` | `.opening (.field γ)` |
| 27 | `.opening (.scalar v)` | `.opening (.field κ)` |
| 28 | `.opening .unit` | `.opening (.field τ)` |
| 29 | `.opening (.poly Q)` | `.opening (.field αopen)` |
| 30 | `.opening (.final F)` | `.opening (.set S)` (q22; failure ∅) |
| terminal, no challenge | `.opening .opening` | none |

This is the intended honest inner-message schedule, not a claim that the parser forbids every other inner semantic payload at rounds 0–13. It validates outer semantic tags, C2 at 2 and polynomials at 14–23 (SemView:90–106,123–136; SemDecision:100–109). Every actual message remains in the view.

`TypedContext` supplies `pub`, all 29 full words W, and subfield typing (SemView:58–67); lanes 26/27 are replaced by the round-2 C2 words (SemView:69–78); D is lane 28 and remains in the initial context. `Lambda x.W` is a derived candidate list, **not an extra transmitted message**; early candidates use zero-padded C2, later candidates use current/parsed C2 (S/SemD2.lean:38–60; soundness LOG:2521–2585). Semantic trace-derived C1 words, H1/G C2 words, ten round polynomials, point claims, OOD values, inactive sum/scalar, relation polynomial and final coefficients can depend on the witness and tape. Empty/unit tags carry no payload. Route-A terminal `opening` is a nullary tag: actual Merkle openings/salts/frontiers live in the later byte projection, not secretly in that constructor (O/Protocol:127–135).

The soundness protocol stores `(challengeValue, duplexState)` at every row (pinned SemD3Glue:938–964), but its decision uses `valuePrefix` to project to values (101–103). `combinedSampler` uses the model's sampler operations: rows 0–29 are absorb/squeeze/advance; row 30 is absorb plus eight squeeze/advance pairs (537–548). The interactive obligation must use their **fresh-answer** law, not a memoized FS oracle nor an assumed uniform field law. Semantic scalar decoding is the embedded QM31 one-block modulo sampler, not the opening WideExact decoder (S/SemD2.lean, `qm31Sample` / `semChal`; soundness LOG:2255–2288); opening `σQ` uses nonzero gamma then ordinary field sampling (C/V3/DuplexQ:34–37). The pinned G20 circle sampler uses the older sentinel policy; live G22 changes this to two nonrational fallback points with modulo slack (LOG from 3134 onward). This job does not freeze either policy or claim its Rust refinement.

The reused relation is **literally** `sourceData.paymentWitness = fun x t => InputNoteExtracted x.pub t` (pinned S/SemD3Glue:87–97), whose existential input-note/nullifier/anchor statement is S/Semantics:73–80. It is weaker than asserting all positive-transfer semantics for arbitrary traces; no stronger relation is silently substituted in Z1.

## Phase 0.3 — Rust mask mechanism and displacement condition

The requested `crates/aspis-statement/src/state_only_*.rs` files consume/verify mask expressions; entropy generation/application actually lives in `aspis-prover`, with pair-forest mask eligibility under `aspis-statement/src/pool_v1/`. All following line numbers are at the pin above.

1. **Eligible trace cells and addition.** `crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs:221–253` selects relation-free Poseidon padding and unused auxiliary cells. `crates/aspis-prover/src/state_only_hiding.rs:619–643` passes that layout and forest copy-active rows to `build_mask_material_for_layout`; `:429–480` expands C1 masks, ten mask-only columns, G and H1 padding. `:676–722,762–773` adds masks only at selected cells, then overwrites one inactive dependent per semantic column to make its inactive sum zero. This is an affine constrained mask space, not independent noise at every committed word/cell.
2. **Expansion and balances.** `state_only_hiding.rs:388–402` hashes domain, precommit binding, encoded context and private entropy; `:340–366` expands counter blocks and rejects invalid M31 limbs (bounded retries). `:169–196,448–472` implements negative-sum balancing. H1 padding is zero on active copy rows; `:297–302` applies it after λ/χ. `v6_onefold_prover.rs:1206–1243` applies masks, concatenates the ten columns, encodes and commits C1; `:1244–1335` derives λ/χ, builds/pads H1, and commits C2. `state_only_candidate_prefix.rs:500–524` independently exhibits λ/χ before `(H1,G)` C2.
3. **D.** `state_only_entropy.rs:426–431,634–674,703–715` derives a separate-domain D expansion from the field source seed and balances inactive rows. `v6_onefold_prover.rs:1127–1140,1311–1324` derives it and commits `[H1,G,D]` as the source C2 tuple; `:687–703,1473–1481` exposes its three point evaluations as column 28. It is absent from the H-mask functional (`crates/aspis-core/src/state_only_hiding.rs:612–657`), so it is not a blanket additive pad for every semantic disclosure. The soundness model instead keeps lane 28 D in initial W and adapts only lanes 26/27. The correspondence/commitment timing must be decided in a future refinement; no equivalence is assumed.
4. **Mask expression versus R0 terminal.** `crates/aspis-statement/src/state_only_terminal.rs:797–812,844–871` computes `mask + eta * original`; `crates/aspis-core/src/state_only_hiding.rs:612–657` supplies the mask functional. The unmasked candidate is explicitly labelled a read-only upstream-HVZK probe (`state_only_terminal.rs:959–1001`). R0's terminal is `eq(zc,α) * sum θ^i lane_i + μ H1 + μ² (1-active) H1` (S/SemDecision:73–80) and its 24 scalar rounds have no eta/initial-mask-claim row. Therefore the historical mask wrapper is not already an honest-prover definition for this R0 model.
5. **Salts.** `state_only_entropy.rs:568–585` binds the salt to the complete attempt context and leaf index. `v6_onefold_prover.rs:949–962,995–1022` uses the same derived salt at a fibre in both C1 and C2, with separate leaf hash tags; salt bytes are disclosed only for selected paired openings in the historical public projection (P/PUBLIC_VIEW:10–12,39–41). The retained caller's forest/legacy dispatch has not been authenticated against the missing generated target; the audit identifies the APIs, not a completed production adapter.
6. **Exact claimed mask-image condition.** P/PRIVACY_LEDGER.md:29–36 says the **complete conditioned allowed-witness displacement** must remain in the remaining mask image. Thus it concerns same-allowed-public witnesses after earlier disclosures and the actual schedule, not merely rank of a raw observation matrix. No matrix, conditioning event, or hypothesis is chosen here. P/VALID_PAYMENT_QUANTITY.md:8–22 gives the six-nonzero-coefficient opened-value functional and its 384-row support; :38–53 gives the surviving inverse-product term `170822063 * inverse(recipient_value * change_value)` after the positive repair. The tested final value is seed-invariant (:55–59), but changes to amount splits change public commitments/afterstate: the source expressly does **not** supply a same-public distinguisher or a global ZK failure (:61–76).

### Phase 0 exit

All three requested inventories can be sourced at the explicitly separated document/Rust/model boundaries above. The path correction and known source/model mismatches are recorded rather than filled by assumptions. Phase 1 may proceed as an uninstantiated model skeleton. No numerical epsilon, mask-image hypothesis, computational assumption, or privacy theorem follows from Phase 0. The missing historical generated closure is not required to state the interactive-model obligation and is deferred to the expressly later Rust refinement.

## Phase 1 — checked skeleton, no security result

`lean/R0Z/StatisticalDistance.lean` defines uniform finite-tape mean, point laws, finite image supports, equal laws, and rational total variation `dist f g = (sum over support f union support g of |law f - law g|)/2`. The output type need not be finite, so polynomial messages do not force an artificial polynomial-degree/finite-message premise. It proves only nonnegativity, zero for equal laws, and triangle, with two private support lemmas. Finite sums/image supports are symbolic over generic types. No concrete universe, state, trace, row or transcript is evaluated.

`lean/R0Z/ZkStatement.lean` supplies:

- `HonestProver` with witness/tape types, valid relation, causal messages indexed by `i : Fin 31` and a `Fin i.val` challenge prefix, and final-message/output operations. The extra statement argument permits public-input-dependent operations. `honestRows` recurses only on the round counter; `honestView` retains the entire 31-row model transcript and terminal message.
- `PublicOutputs`, `PublicView`, and witness-free offline `Simulator`. TypedContext/Msg/Chal are aliases of the actual model types; full W and C2 words remain visible. Explicit byte/length/event/status fields record the Phase 0 output inventory without pretending that a serializer has been implemented. The raw proof bytes also retain any framing not separately named.
- `ModelSamplers` with actual sampler operations, an uninstantiated finite-tape draw operation, and the public challenge projection. `SamplerLaw` requires equality with `independentMean` of each actual sampler program. It is a **goal inside HVZK**, not a supplied law/premise. Thus a fake constant challenge generator cannot discharge HVZK by omission of the real sampler law. No FS table is used in the interactive execution.
- `HVZK`: validity alignment with `sourceData.paymentWitness`, the sampler-law goal, and, for every statement/valid witness, the rational total-variation bound between honest and simulated views on nonempty finite prover/simulator/verifier tapes. The means are unconditioned. `epsilon_zk` is an unassigned rational parameter. Equal laws can later discharge distance zero; no equality or bound is proved here.
- `ROMView` and `FSExperiments`, retaining observer queries and full 256-bit answers, with abstract real compilation and simulation-composition operations taking the same prover/simulator objects. `ZK_FS` states the separate distinguishing-advantage target for the not-yet-chosen adversary/game data and symbolic `epsilon_fs`. There is no assumed computational primitive or HVZK-to-FS implication.
- Field-generic `Obligations := HVZK ∧ ZK_FS`. `proverForSource` installs `valid := s.paymentWitness` directly. `combinedSamplers` uses `SemD3Glue.combinedSampler`, whose value is exactly `combinedProtocol.samp`, and projects the internal value/state pair by `Prod.fst`. `R0Obligations` specializes to the current reference field, `Trace` witness, actual `sourceData B`, and that combined sampler. Neither a mask-image premise nor a privacy proof is a parameter. Only ordinary field/typing and finite/nonempty tape instances are structural requirements.

The uninstantiated operations remain meaningful open work: the type checker does not certify their source correspondence, honest acceptance, efficiency, output consistency or privacy. Public success/abort values are part of the law. Pre-protocol entropy/reservation failures and early partial disclosures need a source-level partial-transcript adapter; the fixed total interactive model is not silently claimed to implement those failure paths.

### Concurrent soundness completion / dependency pin

During Z1, the lead's G22/G21/G23 continuation completed and froze at repository revision **`5c8bfe6c5a1be00124d0469459134f028ee22e4a`**. The continuation from LOG:3349 through Freeze was read. Z1's final wrapper imports this checked current source, not the earlier sentinel object. Its key hashes were matched with the host: `SemD3Glue` `6e17304965d8d6771475e85b38796d044abe1f2a634f336efdbad4b2f310475d` (accepted 2724), `SemView` `01868627189632007beaac02e9036d71d4f268dfe9c3f4d8b51ee9964de528e1` (2711), `R0C.SemStatement` `065e73821e28582b1e08073fb64383f0bec7342cf8fed0cbbe3bd68430fab90d` (673). Their already-compiled objects were reused. Phase 0's historical/pinned citations remain at the entry revision; this explicit second pin records the actual compilation dependency boundary.

The current model's decoder identities select `semChal`, `circleSample0`, `circleSample1`, and `σQ` at the established offsets. The fallback correction and its modulo slack are inherited source facts, not a new privacy-policy choice. No Z1 edit was made to the soundness tree, old privacy tree, or Rust. No soundness manifest replay was repeated.

### Lead decision needed — stop list

1. **Lead decision needed: fixed public statement versus random commitments.** The literal model statement includes all W, and the simulator receives it. Decide how application statement/afterstate relates to an honest randomly generated TypedContext, and whether a separate commitment/view refinement is needed. Conditioning on witness-dependent W must not silently turn a strong application-privacy target into a vacuous leakage allowance.
2. **Lead decision needed: witness domain and honest construction.** The reused relation is exactly `InputNoteExtracted`, not a full positive-transfer relation on arbitrary traces. Specify the honest operations for every witness admitted by this fixed relation, or approve a separately justified relation/interface change. Z1 does not strengthen or weaken it.
3. **Lead decision needed: masks for the actual R0 semantic protocol.** Decide the honest masking construction and its link to C1, adaptive H1/G, D, sumcheck polynomials, point/OOD claims and opening messages. The old `mask + eta * original` wrapper and initial mask claim are not rounds in this 31-round model. Decide the D timing refinement (initial lane 28 versus Rust C2 `[H1,G,D]`) explicitly.
4. **Lead decision needed: allowed-witness displacement / mask image.** Specify the same-public witness relation, complete prior disclosures, conditional remaining tape/kernel and bad histories, then prove the claimed image condition. No raw-rank or tested-seed argument licenses it, and no such condition has been inserted into `HVZK` as a premise.
5. **Lead decision needed: tape law and bounds.** Choose ideal mask/field/salt tapes versus bounded byte/seed expansions, their dependence, retry limits, entropy failure and reservation outcomes. The generic representation averages uniformly over a finite nonempty underlying tape; it does not claim uniformity of expanded coordinates or conditioned accepted tapes. Sizes and the concrete `draw` operation remain unspecified.
6. **Lead decision needed: exact interactive sampler instance.** Supply/freeze the reference duplex encoding/labels and the already-authorized scalar/circle/opening decoder identities for `p`; define a finite-tape realizer and prove `SamplerLaw` for its 31 rows, retaining the q22 failure output. This goal is not replaced by ideal-uniform field sampling or by old Rust OOD retry laws.
7. **Lead decision needed: public-output and failure adapter.** Fix exact statement/afterstate/profile/release/account encodings, attempted publication and lifecycle visibility, length reporting, and the partial-transcript shape for preflight/early failures. Authenticate the source envelope and generated byte partition at the eventual Rust pin. No abort, failed retry, or visible attempt count may be conditioned away.
8. **Lead decision needed: simulator and privacy notion.** Construct the witness-free simulator and decide any efficiency/resource requirement beyond this statistical interactive target. A type `simRand` and a function are only an interface, not an efficient algorithm. Decide the rational `epsilon_zk` target (including whether equality of laws is required); no value is selected.
9. **Lead decision needed: FS/ROM composition games.** Instantiate the real compiler and simulator composition on one coherent oracle, the adversary class/query bound, chronological programming/cache-hit/conflict semantics, byte encoding and output projection. `FSExperiments` is uninstantiated data; `ZK_FS` is not a theorem saying any arbitrary games are the correct compilation. Prove correspondence before any resulting bound is promoted.
10. **Lead decision needed: computational assumptions and ledger accounting.** Decide whether/how seed, salt and commitment security assumptions enter a later computational statement, and fix `epsilon_fs`, each old ledger term, and their relationship to `epsilon_zk` and total advantage. None is chosen or assigned zero. Model soundness errors are not privacy errors.
11. **Lead decision needed: retry and session scope.** Keep the initial target one session; specify any bounded retry wrapper and later adaptive multi-session experiment with durable nonce reservations and evolving public/oracle history. Conditional release bounds, coupling losses and independence need proofs, not source comments or multiplication of a one-session bound.
12. **Lead decision needed: Rust refinement pin.** Choose/authenticate the eventual concrete generated prover, serializer and application projection; resolve the historical missing generated preimages and current forest salt-dispatch boundary. Refinement is later work. No extraction task is reopened in the old privacy directory.

Z1 stops at this list. No HVZK proof, ZK_FS proof, mask-image hypothesis, epsilon value, computational assumption or privacy release result is claimed.

## Host validation and final review

Host: `dombarker@100.108.41.90`; pinned build workspace `/home/dombarker/project-offloads/aspis-fs-generic-20261006`. Verified Lean 4.32.0, Linux x86_64 release, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`; inherited pinned Mathlib cache `81a5d257c8e410db227a6665ed08f64fea08e997`. Commands: `sh run_g15_lake.sh N R0Z/<target> 7000 7`, the existing run2.sh adapter differing only by invoking `lake env lean -j1 -M7000 -DElab.async=false`. Its run2 reservation/scope code was inspected before use. All four runs admitted 24+7 GiB below 55 GiB and used MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128 and timeout 900 s. One Z1 Lean process at a time, guarded by `/tmp/aspis-r0-z1-lean.lock`; host process checks before the launches found no competing Lean job. No cap increase, package build, generated aggregation, full manifest replay or unchanged rerun.

Source revisions: Phase 0 pins `ab6bbce28a64f8d208c49097ea64713af711321f`; accepted final statement/import closure uses `5c8bfe6c5a1be00124d0469459134f028ee22e4a` plus the exact new-source SHA below. Concurrent soundness commits occurred during development, so per-attempt source snapshots/hashes, rather than an inferred wall-clock HEAD, identify the uncommitted drafts. `StatisticalDistance` depends only on pinned Mathlib; the other target's imported interfaces were checked against the accepted source/cache pins above.

| Attempt | Exact target | Lean/scope exit | time exit | Wall s | Peak RSS KiB | Swaps | Source SHA-256 | Result / axioms |
|---:|---|---:|---:|---:|---:|---:|---|---|
| 3000 | `R0Z/StatisticalDistance.lean` | 0 | 0 | 2.89 | 6,719,992 | 0 | `db9adc3789bc1daa0e377373af5ec4f980c99d8252a40998b772493f0c86defc` | All 10 definition/helper/theorem audits standard; no warnings/errors. |
| 3001 | `R0Z/ZkStatement.lean` | 1 | 1 | 2.77 | 6,782,288 | 0 | `20958ab5e4a24daf5e9bd71911c4ef64868e1e230a05c2dec137dcdbd073ea96` | Missing `[Field K]` on Chal alias. Corrected binder; failed audit error terms rejected. |
| 3002 | `R0Z/ZkStatement.lean` | 1 | 1 | 3.26 | 6,823,112 | 0 | `ebd6c69850b25a20eafeeadd2745cd2407cb6a6c0638e4ff34a16e74f9e7a393` | Concrete source wrapper added; typeclass search did not reduce its rand projection. Changed constructor from def to abbrev. Failed audit error terms rejected. |
| 3003 | `R0Z/ZkStatement.lean` | 0 | 0 | 3.40 | 6,858,980 | 0 | `2a2a21f955083a3da6b1f7fe3d7f5ba4a98edf79d5905df03f21229103c614ae` | All 20 audits standard or empty; no warnings/errors. Final whole-file check. |

Final obligation audits:

```text
'R0Z.ZkStatement.HVZK' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0Z.ZkStatement.ZK_FS' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0Z.ZkStatement.Obligations' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0Z.ZkStatement.R0Obligations' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are audits of **definitions of goals**, not proofs of those goals. The only new mathematical proofs are the three requested distance properties and their two support helpers. Source scan found no authored `sorry`, `axiom`, `native_decide`, `admit`, `maxRecDepth`, `maxHeartbeats`, `#eval`, or `#reduce`; the only explicit `Finset.univ` is the generic symbolic image support. Neither core nor generated source was edited. `git diff --check` passes.

Raw `out-N.log`, `time-N.log`, `sha-N.txt`, and exact `source-N.lean` snapshots remain in the host `evidence/` and hash-verified copies at `/tmp/r0-z1-20261009/evidence/`. Every copied snapshot matches its SHA receipt. Both final local Lean files match their accepted host snapshots byte-for-byte. Z1 evidence stays outside the repository. A concurrent archive operation captured the two final Lean sources and Phase 0/1 report in `052ac60b8b77acf9a6552c485c21b9e426acee6c` while this task was finishing validation. This worker did not create or amend that archive commit or its unrelated contents. The final Z1 commit only completes this LOG; no co-author trailer is added. The archived Lean source hashes equal the accepted snapshots above.

## Lead decisions after Z1 (2026-10-09)

Z1 accepted (host 3000/3003, standard axioms; report and 12-item stop list
reviewed against the cited sources).

Finding driving everything below: the historical reference terminal is
`mask(α) + η · original(α)` (`state_only_terminal.rs:797–812, 844–871`;
mask polynomial `state_only_mask_value` from ten mask-only C1 columns and
the explicit G word, `aspis-core/src/state_only_hiding.rs:612–657`). The
frozen R0 model (Route A) has no η row and no mask-only columns, so its ten
sumcheck round polynomials are degree-27 functions of the trace MLEs and
disclose witness information; only their degree-≤1 part is covered by the
μ·H1 term. The R0 model as proven sound is not expected to be HVZK.

D1 (statement). The privacy statement is `Public K` together with the
commitment handles; the words `W` are **prover output**, not statement.
`TypedContext` remains the soundness-side object derived from the
commitment. In the interactive model the commitment is ideal: the verifier
view contains roots as opaque handles plus exactly the opened positions
(OOD claims, the q22 fibres). Hiding of the ROM Merkle commitment with
salts is a `ZK_FS` term (`ε_commit`), not an interactive premise.

D2 (witness). `witness` := an honest transfer instance; the honest trace
is the reference builder applied to it (plus the mask tape, D3).
`valid x w` := the built trace satisfies `InputNoteExtracted x.pub`
(soundness relation unchanged); this is a completeness lemma to prove, not
a premise. HVZK quantifies over honest instances.

D3 (masking — reference change). The reference protocol regains the
historical masking: ten mask-only C1 columns and the explicit G word
(mask tape uniform over M31 coordinates on the eligible cells of
`pair_forest_hiding.rs:221–253`, with the inactive-sum balancing of
`state_only_hiding.rs:676–773`); a message carrying the mask's hypercube
sum claim, then a fresh challenge η drawn after μ; the sumcheck target
becomes `maskSum + η·0` and the virtual polynomial `mask + η·original`,
with `mask` of individual degree ≤ 27 (`state_only_mask_factors`).
Global rounds become 32 (η at the new index 14, α at 15–24, circle 25–26,
opening 27–31). D stays in the initial context (it is derived from the
seed before λ, χ; commit timing affects binding, not the law) — the Rust
`[H1,G,D]` C2 tuple is a refinement item. Soundness extension (G24, after
Z2): one η row with budget `100·(1+δQ)/P⁴` (a nonzero degree-1 polynomial in
η per list-decoded candidate trace, ≤ 100 candidates; corrected 2026-10-09 from
the coefficient-1 figure first written here), `VirtualDeg` for `mask + η·original`, `HonestRows` with the mask's
Boolean-row values; the FS2 instance grows by one one-block row.

D4 (mask image — the main theorem, Z3). For every fixed public statement,
honest instance and challenge sequence, the disclosed view is
`f(public, challenges) + L(maskTape)` with `L` affine and its image
containing the witness-dependent displacement between any two honest
instances with the same public statement. Stated as `MaskImage : Prop` in
Z2; proved in Z3 from the encoder's linear structure and the mask cell
layout. No raw-rank or tested-seed argument is accepted as its proof.

D5 (tapes). Interactive model: ideal uniform mask/salt/D tapes over the
field coordinates; byte-expansion bias and bounded retries are `ZK_FS`
terms (`ε_seed`, `ε_sampler_abort`), stated, not folded into HVZK.

D8 (notion). Statistical HVZK with target `ε_zk = 0` (equal laws) under
D1–D5; the simulator samples the view's affine part directly. Efficiency
is not a requirement of the interactive statement.

D6, D7, D9–D12: retained exactly as Z1 states them; deferred to the FS/ROM
and refinement phases. No value is assigned to any ledger term.

## Z2 — masked reference modules; stop at D4 (2026-10-09)

Read “Lead decisions after Z1” first. Base and all Rust citations in this
section are **`d2b7413259a75100db9d1c722d88932bfea28fb9`**. Worktree:
`/Users/dominic/ZK/.worktrees/ZK-v8-reference`. Other workers advanced the
branch and edited Rust / the soundness tree during this task; none of those
changes was made, staged, or reverted by this worker. Only the two new Lean
modules below and this LOG are this task's changes. The pinned Rust files
listed below were checked byte-for-byte against the worktree when reviewed.

**Status: items 1 and 2 implemented and host-checked. Item 3 is stopped at
the unresolved formal meaning of D4 below. `ZkStatement.lean` remains the
accepted Z1 file; it is not a 32-round privacy statement and has not been
recompiled or presented as one. No MaskImage, HVZK, completeness, FS privacy,
or extended soundness theorem is claimed.**

### Implemented definitions and exact source boundary

`lean/R0Z/MaskedProtocol.lean` keeps the existing outer
`R0C.SemStatement.Msg` / `Chal` types and extends the inner message with
`SemMsgZ.base` and `SemMsgZ.maskSum`. Its `schedule : Fin 32 → RoundKind` is:

| Round | Message / challenge |
|---|---|
| 0, 1 | empty semantic message / λ, χ |
| 2 | C2 (`h1 h g`) / θ |
| 3–12 | empty semantic message / zc₀…zc₉ |
| 13 | empty semantic message / μ |
| 14 | mask-sum claim / η |
| 15–24 | sumcheck polynomial / α₀…α₉ |
| 25, 26 | point claims then first OOD claims / z₀, z₁ |
| 27–31 | the five opening rows |

C2 is a message before θ, not an additional challenge round. The terminal
opening response remains after the last challenge. This module gives the
schedule and algebraic checks, not a new sampler, commitment projection,
honest prover implementation, or replacement `combinedProtocol` theorem.
`terminalZ` deliberately wraps the **R0** `terminalValue`, including its
μ² inactive-H1 term, with the historical `mask + η·original` form. It does
not replace the R0 terminal with the historical Rust terminal's shorter
`original`. `sumcheckChecksZ` takes a mask claim and 25 semantic challenges,
checks degree ≤ 27, starts at `maskSum + η·0`, and ends at `terminalZ`.

`maskValue_mldeg` proves `SemBadSets.MLDeg 27 10` **after substitution of
the committed trace MLEs** (`honestClaims t α 0` in lanes 0–25 and 27).
The proof bounds each dense linear form by degree 1, its powers by degree
26, and multiplies by the existing degree-1 MLE bound. It uses the `VDeg`
calculus symbolically. A proof only holding the column evaluations constant
would miss the extra MLE degree needed by the virtual polynomial.
The tower coefficients reuse `PackBasis.i/u`, exactly the soundness model's
abstract `(1,i,u,iu)` interface; no new tower equation or Rust arithmetic
refinement is assumed.

`lean/R0Z/MaskLayout.lean` defines the literal eligibility predicate for
semantic columns 0–15, a separate full-domain tape for columns 16–25, and
four base-field tape coordinates for each G/H1-padding/D sample. Thus the
tape has type `MaskTape K F` for the base subfield `F : Subfield K`;
semantic masks are not silently sampled over the larger extension field.
Salts do not affect `applyMask` and are outside this trace-mask tape.
The ideal tape includes redundant coordinates that balancing discards,
and unused H1 coordinates that the active-row projection discards. It is
not a byte-seed expansion claim.

`applyMask B t tape` adds eligible C1 masks then balances each semantic
column, installs the ten separately balanced mask-only columns and G/D,
and adds the inactive H1 padding. Here `t 26` is the **supplied adaptive
H1 table**: `applyMask` does not construct H1 before λ/χ. `dWord` is a
separate operation available for initial lane 28 before those challenges,
as D3 requires. All row sums remain symbolic.
`applyMask_affine` proves preservation of the affine combination
`a • p + (1-a) • q` over **F**, for every fixed trace and every `a : F`.
It is an affinity theorem for this operation, not a mask-image or honest
trace preservation theorem.

### Citation ledger (all at the Z2 base)

Abbreviations here: **C** = `crates/aspis-core/src/state_only_hiding.rs`;
**M** = `crates/aspis-prover/src/state_only_hiding.rs`;
**E** = `crates/aspis-prover/src/state_only_entropy.rs`;
**F** = `crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs`;
**H** = `crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs`;
**P** = `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs`;
**S** = `docs/research/v8-r0-sem-proof-20261008/lean/R0P/`.

| Definition / fact | Citation |
|---|---|
| Inner semantic constructors; outer tags; C2 timing | S/SemView.lean:30–34,53–67,83–91; `docs/research/v8-r0-close-20261007/lean/R0C/SemStatement.lean:18–33`; fixed D3 above supplies the extra row and shifted indices. |
| 29-lane trace, lane allocation, public type | S/Core.lean:20–23,55–67. |
| Abstract tower coefficients `(1,i,u,iu)` | S/CoreExt.lean:30–39; C:436–465,535–552 (`mul_tower_basis`, basis). |
| Semantic exponent schedule | C:391–393: family 0, exponents `[0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25]`. |
| Ten mask-only exponents | C:394–395: `[1,3,5,7,9,11,15,17,19,21]`. |
| G family / exponent | C:396–397,528–533: family 16, exponent 26, factor `1 + L16^26`. |
| Linear forms, power table, factors | C:472–492,494–512,561–580. `maskLinear family α = Σ_j (3+22j+family(17+8j)) α_j`. |
| Mask value, selected mask-only terms, optimized selected evaluator | C:612–643,647–674. Horner's implementation uses the same exponent/tower coefficients; no operational equivalence theorem is claimed here. |
| Historical wrapper and mask-only lane selection | `crates/aspis-statement/src/state_only_terminal.rs:797–812,824–871`. |
| Original R0 terminal and sumcheck checks | S/SemDecision.lean:73–98. New challenge indices are D3's, not the old `14+j`. |
| Functional degree machinery and honest MLE bound | S/SemDeg.lean:13–144 (VDeg/constant/monotonicity/add/multiply/powers/sums/MLDeg), :473–481 (`vdeg_honestClaims_zero`); S/SemD3.lean:29–31 (`honestClaims`). |
| Forest geometry and used path cells | F:36–45,54–75,204–218: 57 Poseidon blocks; 24 private directions, path bases at local rows 1,5,9,13; value block 63. |
| Exact eligibility | F:221–253; H:23 (padding begins at local row 13); P:223–225 (16 semantic columns, 1024 rows, 16-row blocks). |
| Translated value/occupancy auxiliary predicate, including legacy path helper | H:289–334; P:230–265,343–354. The forest subtracts 48 before calling it (F:228–229). |
| Copy-active registry for balancing | F:179–201; `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs:4–5` (fingerprint `0xdf394a5a8554d09c`, active masks); S/CopyConstants.lean:30–31 and S/Copy.lean:238–246 reuse it. |
| Dependent-row selection and balancing | M:169–196,448–472,699–715. First inactive row is 0 (first active mask 6144 has bit 0 clear); last eligible inactive row in every semantic column is 1023 (F:221–253/H:289–334 leave it unused; last active mask 1749 has bit 15 clear). These two endpoint checks do not enumerate rows. |
| C1 addition, mask-only/G outputs, forest adapter | M:676–722,762–773. |
| H1 padding support and application | M:465–472,297–302 (forest adapter). |
| D word and forest adapter | E:634–674,703–715: separate domain from the source seed, four-limb samples, first-inactive negative-sum balance. D3 fixes its model timing; the source C2 timing remains a refinement item. |

Pinned SHA-256 for the Rust sources used above:

| Source | SHA-256 |
|---|---|
| C | `18058112db3108a18f9d11f8d9ffb6f9c1b310b90b333010fd0f98cac480237f` |
| M | `48dddafce0ea55d5df2f6b670cd8c571cd182e446ce34ea8b3d42aa313b32d3f` |
| E | `78ebbb3176daf23935243452992548ff9d877aaaf853d73e5ee46b60d8cb3ec0` |
| F | `61bcd59a22c9c02fe3f9ba69cda43bfa8fe02ea14f15da9b761e976fe48798bf` |
| H | `3dfe485fc2e9a643a15e0bc7ef0d9fed20b1fa43984bb1d0997d38a380a90ab6` |
| P | `8a7a4c7bdd3fe0ecd14d6fc920182be434ab92536924de22d269d906be3387b2` |
| Forest copy constants | `cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50` |
| Historical terminal | `1e4ae2058a92c0c8fb6217144ac0c092e233ab4dd8f4e63a85cdab7b2ae121a5` |

### Lead decision needed — D4 formalization stop

These are unresolved quantifiers/objects in the fixed D4 text, not a request
to reopen the accepted D1/D2/D3/D5/D8 choices. D4 says the disclosed view is
`f(public, challenges) + L(maskTape)` for each fixed public statement,
honest instance and challenge sequence, and asks for a witness displacement
in its image. Before writing `MaskImage : Prop`, the following need an
explicit choice:

1. **Lead decision needed: witness dependence of the affine map and offset.**
   Is there one `L(public, challenges)` shared by every same-public honest
   instance, or an `L(public, instance, challenges)` for each instance?
   With both `f` and `L` independent of the instance, the stated identity
   requires equality of the views for the *same tape*, stronger than equal
   laws and leaving no witness displacement. Allowing an instance-dependent
   affine `L` has a different quantifier order and allows its linear part
   (and resulting distribution) to vary with the instance. A formulation
   with a witness-dependent offset and a shared linear mask map,
   `view(w,r) = b(w) + A(r)`, would make the usual displacement explicit,
   but changes the written `f(public, challenges)` dependence. This worker
   has not selected any of these propositions.
2. **Lead decision needed: define the displacement and the relevant image.**
   For an affine `L`, `Set.range L` and the range of its linear part
   `r ↦ L(r) - L(0)` are different objects. For example, the affine image
   `{(r,1)}` does not contain the zero displacement, whereas its direction
   space `{(r,0)}` does. D4 does not say whether the displacement is the
   difference of zero-tape views, unmasked views, or views after a specified
   conditioning, nor whether “image” means the affine image itself or its
   direction space. This distinction determines the exact Lean goal; it
   cannot be silently resolved by an assumption or a rank condition.

Per Z2's explicit stop rule, item 3 has not been partially rewritten around
one interpretation. `ZkStatement.lean` and `StatisticalDistance.lean` are
byte-identical to Z1 (hashes in its table above). D8's target remains perfect
HVZK (`ε_zk = 0`); no ledger error, computational assumption, sampler law,
or source refinement was chosen. The next step is the lead's precise D4
formula, followed by the requested statement restructuring and its focused
31xx host check. This is a definition boundary, not a failed privacy proof.

### Z2 host validation

Host/workspace and runner are the same as Z1:
`dombarker@100.108.41.90:/home/dombarker/project-offloads/aspis-fs-generic-20261006`.
Reinspected `run_g15_lake.sh` and its Python launcher before use: the
`run2.sh` reservation/scope adapter invokes `lake env lean -j1 -M7000
-DElab.async=false`, with MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0,
TasksMax=128 and timeout 900 s. Each attempt reserved 24+7 GiB below 55 GiB.
The same `/tmp/aspis-r0-z1-lean.lock` serialized this worker's Lean jobs.
Initial process inspection found no competing Lean process; an end-of-task
comparison of the host's `sha-N.txt`/`out-N.log` timestamp intervals found
no overlap of these four attempts with any other recorded attempt.

Reverified Lean 4.32.0 Linux release,
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, and Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`. Existing cached dependencies
were reused. Host source copies of `SemDeg`, `SemD3`, `SemDecision`,
`SemView`, `SemSource`, `CoreExt`, `Copy`, `CopyConstants`, and `Core`
were compared byte-for-byte with the Z2 base and local files; all matched.
No dependency build or full manifest replay was run.

| Attempt | Exact target | Lean/scope exit | time exit | Wall s | Peak RSS KiB | Swaps | Source SHA-256 | Result / axioms |
|---:|---|---:|---:|---:|---:|---:|---|---|
| 3100 | `R0Z/MaskedProtocol.lean` | 1 | 1 | 3.11 | 6,793,420 | 0 | `d56dbbf5e90e687ec69b2d822e2c4edf3b08ea919a2584d3adc8001f1708bcd0` | `vdeg_add` could not infer both degree vectors from the constant result bound; fixed explicit vectors. Failed error-term audit rejected. |
| 3101 | `R0Z/MaskedProtocol.lean` | 0 | 0 | 3.82 | 6,826,908 | 0 | `e2d41ab912aa178f4c24636ce6fde0e9c18e2f4715ac4b138d4b7eb3f4fed84f` | 14 audits standard; no warnings/errors. |
| 3102 | `R0Z/MaskLayout.lean` | 1 | 1 | 5.21 | 6,793,136 | 0 | `bd08b3b45b196569d05efb5adab8d6990f906bf8ca19971cf0ff711b5c6d9843` | Pointwise rewrite did not rewrite an unapplied word under `balance`; fixed by function extensionality. Failed error-term audit rejected. |
| 3103 | `R0Z/MaskLayout.lean` | 0 | 0 | 5.84 | 6,827,388 | 0 | `2c2db6335f1eb0288826fffa541c1826ea760516de2f946c624dabbaa928759d` | 11 audits standard; no warnings/errors. |
| — | `R0Z/ZkStatement.lean` (Z2 restructuring) | — | — | — | — | — | unchanged Z1 hash | Not attempted: D4 stop above. |

Exact proof audits:

```text
'R0Z.MaskedProtocol.maskValue_mldeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0Z.MaskLayout.applyMask_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Raw `out-N.log`, `time-N.log`, `sha-N.txt`, and `source-N.lean` snapshots
remain in the host `evidence/` directory. Each snapshot's SHA matches its
receipt; final local sources match the accepted 3101/3103 hashes. No cap
increase or unchanged retry. The only explicit `Finset.univ` uses in the
new source are symbolic VDeg sums over coordinates/columns, never evaluated
row/state/trace universes. The inactive-row sum is kept abstract under
`balance`. No authored prohibited proof command or option, `#eval`, or
`#reduce` occurs. `git diff --check` passes.

### Lead decision D4′ — exact form of `MaskImage` (resolves the Z2 stop)

Z2's `MaskedProtocol` and `MaskLayout` are accepted (port checked against
`state_only_hiding.rs` 392–395, 484–512, 561–580, 612–645). The two D4
questions are answered as follows; this replaces the prose of D4.

1. **Instance-dependent affine map, shared nothing.** For a public statement
   `x`, an honest instance `w` with `public w = x`, and a challenge vector
   `ch`, the honest disclosed view as a function of the mask tape is affine:
   `view x w ch r = b x w ch + A x w ch r`, where
   `A x w ch : MaskTape K →ₗ[K] View K` is a linear map and
   `b x w ch := view x w ch 0` (the zero-tape view). Both `A` and `b` may
   depend on `w`. No identity between views of different instances at the
   *same* tape is asserted anywhere; only laws are compared.
2. **Image = range of the linear part; displacement = zero-tape difference.**
   ```
   MaskImage x : Prop :=
     ∀ w w' ch, public w = x → public w' = x →
       LinearMap.range (A x w ch) = LinearMap.range (A x w' ch) ∧
       b x w ch - b x w' ch ∈ LinearMap.range (A x w ch)
   ```
   Equivalently: for every challenge vector, all same-public honest instances
   have the same affine coset `b + range A` of views.
3. **Why this is the right statement.** With the tape uniform on the finite
   space `MaskTape K` (D5), the law of `view x w ch` is the uniform law on the
   coset `b + range A` (every fibre of an affine map is a translate of
   `ker A`, so all fibres over the coset have equal size). Equal cosets give
   equal laws; hence `MaskImage x → HVZK_perfect x` is a generic finite
   linear-algebra lemma (no sampler or source fact), and the simulator is the
   honest prover run on any instance `w₀` with `public w₀ = x`
   (`Classical.choice`; if no such instance exists the statement is outside
   the language and HVZK is vacuous). Conditioning on `ch` is what the
   `∀ ch` quantifier does; D5 makes the challenge law instance-independent, so
   equal conditional laws give equal joint laws.
4. **Obligations.** `Obligations x := MaskImage x ∧ Completeness x`, with
   `HVZK_perfect x` and `ZK_FS x` *derived* (`hvzk_perfect_of_maskImage`,
   and ZK_FS from HVZK_perfect under the ROM view of D5). `MaskImage` itself
   (Z4) is the rank statement that the Rust q29 rank gate measures
   (`state_only_hiding.rs:555–560`); it is the only privacy obligation that
   depends on the layout.
