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
