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

### Lead decision D4″ — tape split (resolves the Z3 affinity stop)

Finding accepted: the honest sumcheck round polynomials are not affine in the
eligible-cell noise. `g_j(X) = Σ_b V(α_{<j}, X, b)` evaluates the virtual
polynomial at non-Boolean prefixes, where selector MLEs are nonzero and
`MLE(succ(X))` is a combination of every row, so a relation-free cell such as
(column 0, row 13) enters `g_j` polynomially (degree ≤ 25 through the pow5
chain). This is a property of sumcheck, present in the Rust prover too; it
does not affect completeness or soundness (Boolean-row constraints are
untouched) and it is not what the mask-only design relies on.

Decision:
1. `MaskLayout.MaskCoordinate = EligibleCell ⊕ (maskOnly ⊕ GD)` is split.
   The **affine tape** is `AffTape := (Fin 10 × Fin 1024) ⊕ (Fin 3 × Fin 1024 × Fin 4)`
   (mask-only columns, G and D). The **eligible-cell noise**
   `e : EligibleCell → F` becomes part of the honest instance:
   `HonestInstance := Instance × (EligibleCell → F)`, with `public (w, e) = public w`
   and `build (w, e) := applyEligible (build w) e`.
2. `view x (w,e) ch : AffTape → View K` is the object D4′ decomposes:
   `view = b + A r` with `A` linear in the affine tape. Every disclosed
   component is affine in it: `maskValue` is linear in the mask-only and G
   claims (MaskedProtocol), the mask-sum claim is linear, OOD/zerocheck
   claims are MLE evaluations (linear in cells), opened positions are
   codeword symbols (linear in cells), and the original's round polynomials
   are independent of the mask-only/G/D coordinates and affine in the
   H1-padding coordinates (`μ·H1`, `μ²·(1−active)·H1`, `active` tape-free).
   (Corrected after Z3's check; the first draft said "independent".)
3. `MaskImage x` keeps the D4′ form, quantified over honest instances of the
   new type (so over `e` as well). `A` is expected to be independent of the
   instance (the mask factors depend only on α) — Z3 may prove and use
   `A x (w,e) ch = A x (w',e') ch` but must not assume it.
4. HVZK: for each fixed `e`, the uniform-coset lemma gives the conditional
   law; `e` is uniform and instance-independent (D5), so equal conditional
   laws give equal joint laws. The simulator still runs the honest prover on
   `Classical.choice` of an instance (now including an `e`) for `x`.

## Z3 — stopped by the semantic sumcheck affinity check (2026-10-09)

Ran `git fetch` first and read D4′ from the requested base
**`9a9a2b3ff`** before inspecting other sources. D4′ resolves both Z2
questions; neither is reopened here. The worktree had already advanced to
`2363f469444bd383a352d5a5f43016cc98e2044d` (the eta-budget correction).
All source citations below refer to git objects at **9a9a2b3ff**, not to
concurrent soundness edits. This task changes only this LOG.

**Stop: the last semantic sumcheck polynomial, message `roundPoly p₉`
at global round 24, is not affine in the full `MaskLayout.MaskTape`.**
Its dependence on one eligible semantic C1 mask coordinate has degree 25.
`applyMask_affine` is valid, but composition with the semantic oracle is
not affine. Thus the requested `view_affine` cannot be obtained by the
proposed argument for the actual disclosed messages. The instruction was:
“if some message is not affine in the trace … stop and name it.” No
unproved affinity premise, assumed linear map, or replacement transcript
has been installed. No claim of a privacy attack or failure of HVZK is made;
this obstructs the proposed affine-map reduction.

### Message-by-message audit

Abbreviations in this section: **Z** = this directory's `lean/R0Z/`;
**S** = `docs/research/v8-r0-sem-proof-20261008/lean/R0P/`;
**O** = `docs/research/v8-wide-reference-20261005/lean/R0/`;
**P** = `crates/aspis-prover/src/`. “Linear” below describes the inspected
field-payload formulas at fixed challenges, not a new kernel-checked theorem.

| Disclosed component | Affinity check and source |
|---|---|
| Empty semantic messages / ideal commitment handles | Empty messages are constant. D1 treats handles as opaque metadata; this is not a claim that a Rust Merkle hash is affine. The source word-valued C2 message must still be projected to handles in the eventual ideal view. S/SemView.lean:30–34,58–76; D1 above. |
| Mask-sum claim, row 14 | Linear in the trace: each mask factor at each Boolean row is fixed; the claim is a sum of factor times cell value. Z/MaskedProtocol.lean:69–84; P/state_only_hiding.rs:845–882. Composition with the affine mask operation stays affine. |
| **Semantic round polynomials, rows 15–24** | **Fails.** These are partial Boolean sums of `mask + eta * original`, interpolated in the current challenge coordinate. The original oracle has nonlinear Poseidon trace expressions. The final round has no remaining Boolean sum, so evaluating its message at 1 exposes the explicit degree-25 dependence below. Z/MaskedProtocol.lean:123–148; S/SemD3.lean:28–38; S/Sumcheck.lean:19–30; P/state_only_zerocheck.rs:79–121 and P/state_only_hiding.rs:900–931. |
| Three point-claim vectors, row 25 | Linear functionals of the trace at fixed alpha, successor(alpha), xor12(alpha). S/SemD3.lean:28–30; S/SemView.lean:36–56. Nonlinearity of the successor **in alpha** is irrelevant when challenges are fixed. |
| Circle OOD claims, rows 26/27 | Polynomial evaluation at fixed circle points is linear in the encoded message. O/Chord.lean:34–35,51–63,83–100. This does not claim linearity in the circle points. |
| Opening-layer inactive-sum scalar / unit, rows 28/29 | The scalar is a fixed weighted sum of the batched trace; the unit message is constant. O/OpeningDefinitions.lean:34,50–67; `docs/research/v8-r0-fs-20261006/lean/R0FS/Protocol.lean:9–15,50–60`. |
| Opening-layer degree-6 polynomial, row 30 | Its kernel is bilinear in quotient coefficients and dual weights, but the latter depend only on fixed challenges/positions, not trace values. It is therefore linear in the quotient coefficients. O/RoundNormalization.lean:24–34; O/OpeningDefinitions.lean:53–67,96–97. This is a different polynomial from the nonlinear semantic degree-27 messages. |
| Final folded message and q22 fibre values, row 31 and final response | Fixed-point chord division, batching, radix-four transforms and folding are linear in the word; restriction to the fixed queried positions is linear. O/OpeningDefinitions.lean:36–40,99–106; O/Fold.lean:55–72; O/RoundNormalization.lean:36–40. Salts/handles/authentication metadata still require D1/D5's ideal projection; no Rust commitment theorem is asserted. |

The honest builder remains uninstantiated. This audit does not assume its
completeness or prove H1 construction. The obstruction below holds for
**any fixed input trace** and removes H1 from the terminal with `mu = 0`
and the copy lane with `theta = 0`, so neither missing operation can repair
this message's tape dependence.

### Symbolic obstruction using one permitted mask coordinate

This is a source-level algebraic calculation, **not a new Lean theorem**,
numerical rank probe, or evaluation of a concrete universe. Work in the
reference M31 base field F and extension field K, with the existing
`PackBasis F`. Write the basis elements as `i = B.i`, `u = B.u`; the tape
scalar below is `s : F`.

1. Let `r_s` have exactly one nonzero coordinate: the semantic mask for
   **column 0, row 13**, with value `s`. Set every other tape coordinate to
   zero. This cell is eligible Poseidon padding: Z/MaskLayout.lean:36–58;
   `crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs:233–249`.
   Row 13 is copy-inactive (the first active-row mask is 6144, with only
   bits 11 and 12 set; S/CopyConstants.lean:30–31). Balancing at row 1023
   gives, for every fixed trace `t`,
   `applyMask B t r_s - applyMask B t 0 = s*e_(0,13) - s*e_(0,1023)`.
   This follows directly from the negative-sum replacement in
   Z/MaskLayout.lean:69–73,91–101; all other changes are tape-independent.
2. Fix the MSB-first point
   `a = (0,0,0,0,0,0,2,1,0,1)` and zerocheck point
   `zc = (0,0,0,0,0,0,0,1,0,1)` (the Boolean row 5).
   The multilinear weights at `a` are supported on **rows 5 and 13**,
   with weights `-1` and `2`. Hence the current column-0 opening is
   `c + 2*s`, while all other current columns are independent of `s`.
   The balancing row 1023 has zero weight because its high bits are 1.
   At `successorPoint a` the support is rows 6/14; at `xor12Point a` it
   is rows 1/9. Neither opening reads the perturbation. These are sparse
   bit-weight identities from S/SemDeg.lean:220–242 and
   S/SemView.lean:36–56; no row sum is expanded.
3. The block selector is 1; `low 5 = -1`, `low 13 = 2`, all other low
   weights vanish. Therefore `leadingLow = fullLow = 0` and
   `internalLow = -1` in S/Poseidon.lean:334–352. Only the internal pair
   contributes. Its interpolated round constants are independent of `s`.
4. A first internal round sends the leading degree-5 contribution from
   input lane 0 to `(- (2*s)^5, (2*s)^5, …, (2*s)^5)`. Applying the
   second fifth power and internal linear layer gives degree-25 leading
   contributions `((2*s)^25, -(2*s)^25, …, -(2*s)^25)`.
   This uses exactly `poseidonPow5`, `poseidonInternalLinear`, and
   `poseidonInternalRound` at S/Poseidon.lean:25–28,55–71. Arbitrary
   fixed trace values, shift constants and round constants contribute
   lower-degree terms only.
5. Take `theta = 0`, `mu = 0`, `eta = 1`. Theta selects packed Poseidon
   group 0 alone (S/SemDecision.lean:44–49,74–80); the two H1 terms vanish.
   At these points `eqValue zc a = -1`. Multiplying the internal residual
   by `internalLow = -1`, then by this equality weight, and packing the
   first four lanes yields the coefficient
   **`2^25 * (-1 + i + u + i*u)` of `s^25`** in the original terminal.
   Packing order is S/Poseidon.lean:775–781 and S/CoreExt.lean:30–39.
   This coefficient is nonzero: 2 is nonzero in M31 and `PackBasis.indep`
   forbids `-1 + i + u + i*u = 0` with base coefficients `(-1,1,1,1)`.
6. The added mask is only affine in `s` at this fixed point, by
   Z/MaskedProtocol.lean:69–84. It cannot cancel the degree-25 coefficient.
   Fix alpha₀…alpha₈ to `a`'s first nine coordinates. The last honest
   sumcheck polynomial `p₉(X)` is the oracle at that prefix and X, with
   **no remaining Boolean variables to sum** (S/Sumcheck.lean:19–30;
   the explicit source loop is P/state_only_zerocheck.rs:95–111).
   Consequently **`p₉(1)` has this same nonzero degree-25 coefficient
   in `s`**. Evaluation of a disclosed polynomial at 1 is a linear
   observable of its coefficients. If the disclosed polynomial were
   affine in the tape, this observable along the line `r_s` would have
   degree at most 1. A nonzero polynomial of degree 25 cannot agree with
   an affine function on all of F, since `|F| = 2^31-1 > 25`.

This uses the task's unrestricted `forall ch` target; it neither discards
bad challenges nor invokes a challenge-probability bound. Lambda/chi and
later opening challenges do not enter the displayed term. Relation-free
padding means the Boolean-row constraints survive masking; it does **not**
make the off-Boolean semantic oracle linear in those masks. Likewise Z2's
`maskValue_mldeg` bounds degree in **alpha**, whereas the failed assertion
here concerns degree in the **mask tape**.

### Lead decision needed — Z3 stop list

1. **Lead decision needed: replace the full-tape affinity step.** The
   requested `A x w ch` cannot describe this full disclosed view in its
   message coordinates. A different privacy proof is needed before the
   statement can be wired to the actual protocol: for example a conditional
   affine argument after fixing semantic C1 masks, with a separately proved
   mixture/coupling step, or a direct argument for the nonlinear pushforward.
   These are possible research routes, not implemented choices or premises.
   Omitting semantic polynomials, setting eta to zero, or declaring affinity
   as a field would change the task and has not been done. D4′'s equal-coset
   lemma remains mathematically valid **for affine maps**; it cannot supply
   the missing affinity of these messages. No MaskImage/layout rank work
   was attempted.
2. **Lead decision needed: retain ZK_FS and add a real ROM bridge.**
   Independently, Z1's `FSExperiments.real` and `.ideal` are arbitrary data
   with no law tying them to the interactive views
   (Z/ZkStatement.lean:143–173). Even equal interactive laws cannot bound
   arbitrary experiments: one can distinguish two constant, unequal ROM
   outputs. D5's ideal tape choice does not supply commitment hiding,
   chronological oracle programming, or game correspondence. The minimal
   proposed repair is to **leave the ZK_FS definition intact**, and make
   `zkfs_of_hvzk_perfect` require a separately established ROM correspondence
   bridge: the real and ideal observer views arise from a common,
   witness-independent randomized postprocessing of the respective joint
   interactive views, up to explicitly budgeted game-hop losses. Equality
   of laws then transfers through the common postprocessing and the losses
   bound the original ZK_FS advantage. The bridge must be proved for the
   actual FS/ROM games; assuming it is not a derivation from D5. No bridge,
   loss values, computational assumptions, or weakened ZK_FS was added.

The existing tape uses the base scalar field F (`MaskTape K F`), with K the
extension field. Any eventual affine formulation must respect that scalar
field (restrict the view's scalars to F, or rename the generic lemma's
scalar parameter). Replacing the C1 tape by uniform K-coordinates would
change D3/D5; no such replacement was made.

### Z3 validation and attempt status

The explicit stop occurs before creating or modifying Lean definitions.
`ZkStatement.lean`, `MaskedProtocol.lean`, `MaskLayout.lean`, and
`StatisticalDistance.lean` remain byte-identical to the requested base.
No `AffineLaw.lean` or `Hvzk.lean` was created. There was no Lean process,
new 31xx attempt, host reservation, concrete field/row/state enumeration,
Rust run, source edit outside this directory, or axioms audit to report.

| Target / requested audit | Attempt | Exit | Wall | Peak RSS | Swap | Source revision | Axioms / status |
|---|---|---|---|---|---|---|---|
| `R0Z/ZkStatement.lean`, `view_affine` | — | — | — | — | — | 9a9a2b3ff, unchanged | Not attempted: semantic `roundPoly p₉` is non-affine. |
| `R0Z/AffineLaw.lean`, equal-coset law corollary | — | — | — | — | — | no new file | Not attempted after the item-1 stop. |
| `R0Z/Hvzk.lean`, `hvzk_perfect_of_maskImage` | — | — | — | — | — | no new file | Not attempted after the item-1 stop. |

Validation is pinned-source inspection and the symbolic calculation above,
not a new formal result. `git diff --check` passes. Commit scope is this
LOG only, with no co-author trailer; concurrent soundness work is untouched.


## Z3 continued — split tape and H1 affinity (2026-10-09)

Read D4″ at requested base **`c67262d0453bda8cf7817d83008d9a1fe5e160c9`**
after fetching. The prior Z3 report above is historical: D4″ resolves its
full-tape non-affinity stop by fixing eligible noise in the honest instance.
The soundness worker continued advancing this shared worktree during this
run. Only this privacy directory was edited by this worker.

### Lead clarifications received during this continuation

1. **H1 stays in the affine tape.** The user selected: “Keep H1 padding in
   the affine tape; prove the original affine in it.” The three extension
   slots are G, H1 padding and D. The corrected D4″ item 2 above now records
   this. No independence of the original from H1, or of A from the instance,
   is assumed.
2. **Public metadata is constant in the instance and tape.** The user fixed
   `metadata : Statement → Challenges → Meta`, independent of instance and
   tape by definition (D1 ideal handles; positions from challenges), and
   `View := Meta × Payload`. Only `Payload` is a vector space. The eventual
   HVZK law is the law of the **pair**; the coset lemma applies to the payload
   and transports through `p ↦ (metadata x ch, p)`. No arithmetic is assigned
   to handles or query indices. This is an accepted definition decision,
   not an outstanding question.

### Implemented and checked

`MaskLayout.lean` now defines the index type
`AffCoordinate := (Fin 10 × Fin 1024) ⊕ (Fin 3 × Fin 1024 × Fin 4)`,
`AffTape K F := AffCoordinate → F`, and
`EligibleNoise K F := EligibleCell → F`. Thus the tape is the F-valued
vector on the requested coordinate set; the index set itself is not the
random vector. This preserves D3/D5's base-field law inside extension K.
`MaskTape` retains the original combined coordinates for an exact bridge.

`applyEligible t e` changes the sixteen semantic columns and balances each
at row 1023. **That balance reads fixed semantic cells and eligible noise
only; it reads no affine-tape coordinate.** `applyAff B t r` preserves those
sixteen columns, replaces mask-only/G/D columns, and adds H1 padding. The
mask-only, G, D and H1-padding dependent coordinates remain at row 0.
`applyMask` is now their composition. `applyMask_eq_port` proves equality
with the original Z2 cellwise port, including all dependent coordinates;
there is no distributional approximation or changed balancing policy.
`applyAff_affine` proves affinity over F. The additional coordinatewise
linear map `traceLinear`, zero-tape baseline `traceBase`, and theorem
`applyAff_eq_base_add` package the actual port as `traceAffine` for the
pending view composition. No affinity certificate is accepted as a premise.

`ViewAffine.lean` proves `copyResidual_affine`, `copyEvaluate_affine`,
`laneAt_affine`, `originalAt_affine`, and `originalAt_decomp` for arbitrary
fixed semantic openings. `terminalValue_eq_originalAt` connects this
algebra directly to the soundness terminal. Its copy term is
`active * (PD * (h * CD + CN) - CD * PN)`, so the H1 coefficient includes
`active * PD * CD`, in addition to the two mu terms after theta/equality
batching. PD/CD depend on the fixed semantic openings. This is why this
continuation does not assert `A_instance_independent`. The large copy
registry is opaque in these proofs, and all sums remain symbolic.

### Citation inventory

Rust line citations below are at **c67262d04** (read with `git show` where
necessary); the mask port's original pin and detailed layout citations
remain in the Z2 table above. The referenced arithmetic is unchanged.

| Definition / check | Source |
|---|---|
| Eligible cells and sixteen-column restriction | `crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs:221–253`; Z2 layout citations above. |
| Negative-sum dependent coordinates | `crates/aspis-prover/src/state_only_hiding.rs:169–196,448–472,676–722`; semantic row-1023 balance at 700–715. |
| G, H1 padding and D limb interpretation | `state_only_hiding.rs:460–472`; `crates/aspis-prover/src/state_only_entropy.rs:634–674,703–715`. |
| Apply H1 padding only after helper construction | `state_only_hiding.rs:248–272,297–302`; `crates/aspis-prover/src/v6_onefold_prover.rs:1244–1257,1279–1307`. |
| Copy term is affine in H1 | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/Copy.lean:111–142,234–238`; source `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:339–357,910–972,1048,1068–1072`. |
| Original terminal and theta ordering | `R0P/SemDecision.lean:43–49,73–80` under the preceding soundness path; `ViewAffine.terminalValue_eq_originalAt` is the exact identity. |
| Actual H1 builder can fail at active poles | `crates/aspis-statement/src/logup.rs:192–224`, producer failure at 199–204 and consumer failure at 212–217; forest adapter `crates/aspis-statement/src/pool_v1/pair_forest_semantic_oracle.rs:168–179`. |
| Forest prover propagates helper failure before C2 | `crates/aspis-prover/src/v6_onefold_prover.rs:1279–1290`; H1 padding and helper-sum check follow at 1292–1310; C2 at 1311–1312. |
| Verifier message type, not an honest H1 constructor | `R0P/SemView.lean:30–34`: `SemMsg.h1` receives arbitrary H1/G words. D2 deliberately leaves the instance builder uninstantiated. |

### Lead decision needed — current stop

1. **Total ideal honest H1 at active poles.** The proposed view is total for
   every `ch`, but the cited source's helper uses fallible inverses and
   returns `ActivePole` when a nonzero-weight tuple equals chi. Its caller
   propagates this error before committing C2. This branch depends on the
   instance's compressed tuples, not solely on the public statement and
   challenges. D5 assigns sampler/abort losses to later FS/refinement work;
   it does not specify the ideal helper value on this branch. D4″ establishes
   affinity once the fixed helper table is supplied, but also does not
   construct that table on failed source inputs.

   The lead must choose the ideal totalization (for example the source's
   weighted reciprocal formula interpreted using field inverse, with
   `0⁻¹ = 0`, and source pole aborts left to later refinement), or retain a
   failure outcome and specify its place in the interactive view. The latter
   cannot silently be placed in `metadata x ch`, now fixed to be independent
   of the instance. No restriction to good challenges, success conditioning,
   or epsilon value was introduced. This question was sent to the user and
   remains pending at this stop. An exploratory, uncompiled view draft was
   removed; no totalization has been installed as the model.

The stop is required by the user's “Stop on anything D4′/D4″ doesn't
determine” rule, not an approval requirement. It occurs before the full
honest-view definition. `ZkStatement.lean` remains the Z1 source (SHA below),
and `view_affine`, the coset-law module, marginalisation and
`hvzk_perfect_of_maskImage` are not claimed. `MaskImage` itself was not
attempted. The earlier FS/ROM correspondence stop remains separate and
unchanged; no computational assumption or weakened ZK_FS was added.

### Host validation

Same pinned host/workspace and `run_g15_lake.sh` run2 adapter as Z2:
`dombarker@100.108.41.90`,
`/home/dombarker/project-offloads/aspis-fs-generic-20261006`.
Lean 4.32.0 / `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`. Each launched job used
`lake env lean -j1 -M7000 -DElab.async=false`, MemoryHigh=5G,
MemoryMax=7G, MemorySwapMax=0, TasksMax=128, timeout 900 s. The runner
admitted 24+7 GiB below its 55 GiB ceiling. Host process prechecks delayed
3108 and 3110 while a soundness Lean job was active; those busy preflights
created no SHA receipt or compiler attempt. Only one privacy Lean job ran
at a time. **Final host interval audit found two cross-worker overlaps:**
3104 (09:37:06.747–09:37:13.279 UTC) overlapped soundness 3229
(09:37:08.922–09:37:15.839); 3108 (09:51:04.418–09:51:12.866) overlapped
soundness 3237 (09:51:07.016–09:51:12.052). In each case the other worker
started after this worker's process precheck. The private
`/tmp/aspis-r0-z1-lean.lock` did not serialize that worker's run2 launches.
This is a deviation from the host-wide one-job rule, not an assertion of
compliance: all jobs retained their individual caps and zero reported swap,
but host-wide serialization needs a common lock or exclusive build window
before further launches. No other overlap with 3104–3110 was found in the
SHA/output timestamp audit. No new launch or unchanged replay was made
after this discovery. No package replay or larger cap was used.

Source revision in this table is the requested base **c67262d04 plus the
exact privacy source snapshot identified below**. Accepted 3110 imports
the accepted 3108 MaskLayout. The moving shared branch HEAD is not used
as a claim that uncommitted source was already present in a commit.

| Exact target | Attempt | Exit | Wall | Peak RSS (KiB) | Swap | Axioms / result |
|---|---:|---:|---:|---:|---:|---|
| `R0Z/MaskLayout.lean` initial split | 3104 | 0 | 6.50 s | 6,831,300 | 0 | 17 audits, standard only. |
| `R0Z/MaskLayout.lean` linear packaging | 3105 | 1 | 8.13 s | 6,803,860 | 0 | Scalar-coercion/conditional goals; rejected. |
| `R0Z/MaskLayout.lean` linear packaging | 3106 | 1 | 8.09 s | 6,802,784 | 0 | Local reduction hit the default recursion limit; rejected. |
| `R0Z/MaskLayout.lean` linear packaging | 3107 | 1 | 8.13 s | 6,802,628 | 0 | Invalid irreducibility attribute on an abbrev; rejected. |
| **`R0Z/MaskLayout.lean` final** | **3108** | **0** | **8.42 s** | **6,838,224** | **0** | **19 audits, standard only**, including `applyAff_affine`, `applyAff_eq_base_add`, `traceAffine_apply`. |
| `R0Z/ViewAffine.lean` | 3109 | 1 | 2.92 s | 6,786,760 | 0 | Extra tactic after a closed goal; rejected. |
| **`R0Z/ViewAffine.lean` final** | **3110** | **0** | **3.18 s** | **6,819,472** | **0** | **5 audits, standard only**, including `originalAt_affine`, `originalAt_decomp`, `terminalValue_eq_originalAt`. |
| `R0Z/ZkStatement.lean`: `view_affine` | — | — | — | — | — | Stopped at the honest-H1 definition boundary. |
| `R0Z/AffineLaw.lean`: coset lemma | — | — | — | — | — | Not created after the stop. |
| `R0Z/Hvzk.lean`: HVZK/marginalisation | — | — | — | — | — | Not created after the stop. |

“Standard only” means a subset of `propext`, `Classical.choice`,
`Quot.sound`. Failed elaborations' compiler-generated `sorryAx` audit
output was rejected; no such output is a proof result or dependency of
an accepted audit. No source `sorry`, `axiom`, `admit`, `native_decide`,
recursion/heartbeat-limit override, or concrete finite-universe evaluation
was introduced. The 3106 replacement is symbolic balancing plus a named
pointwise H1-padding lemma, keeping `copyInactiveRows` opaque; 3107's
invalid abbrev attribute was removed without an unsafe reducibility option.
Unused-simp warnings in the final MaskLayout are non-fatal.

| Attempt | Source SHA-256 (also the exact host snapshot SHA) |
|---|---|
| 3104 | `7796f93ed55fca3c86bb80b4a46fbe36232d43a3ef9f56facd6dd94c0b0f75b1` |
| 3105 | `9598f14cd9b619a716bcb5794f0e8d5f21a6f9f2dc8c4290c3e152391d2c89ff` |
| 3106 | `39fe14d256dd83a4c533a7492b6fa31c67c505a2c92ccf4d288bf63552455122` |
| 3107 | `4f61eed64272e453b3a3a9770053faf6f7ed971c8dd224cf85bfc8378cef26d2` |
| 3108 | `4f0615a66f8abe90b80d1cdff56961356cff13628c85dbd3456f43d9f425b43a` |
| 3109 | `f1d277c691c1be05dd710f3b8ca8f4b84282115ea967de14e4e57bb7c4a22324` |
| 3110 | `7719f782cf4a3326f27373d59f378d130e035f3698c6ea0d3379da69fabbe33a` |
| Unchanged `ZkStatement.lean` | `2a2a21f955083a3da6b1f7fe3d7f5ba4a98edf79d5905df03f21229103c614ae` |

Every `evidence/source-N.lean` snapshot was hash-checked against its
`sha-N.txt` receipt. Raw scope/output/time/SHA/source records remain on the
host. The two final local sources equal the accepted snapshots. Commit
scope is these two Lean sources and this LOG only, with no co-author trailer.

### Lead decision D9 — ideal honest H1 at active poles (resolves the Z3 stop)

Totalise. The ideal honest helper is the source's weighted-reciprocal formula
read with the field inverse, `0⁻¹ = 0` (Lean's `Field` inverse), so
`view x (w,e) ch` is total for every challenge vector and `HVZK_perfect`
stays the ε = 0 statement of D8 for the ideal model. The source's
`ActivePole` abort (`logup.rs:192–224`, propagated before C2 by
`v6_onefold_prover.rs:1279–1290`) is a refinement term, recorded here as the
obligation **ZR1**: the real honest prover's view equals the ideal view except
on the event `∃ weighted tuple of the instance equal to χ`, whose mass under
the semantic χ sampler is ≤ (number of nonzero-weight tuples)·(1+δQ)/P⁴; the
statistical distance of the real system from the ideal one is bounded by that
mass (the bound is instance-dependent through the tuple count only, which is
bounded by the trace size, 1024·(columns), so a public bound suffices). No
good-challenge restriction or success conditioning enters the ideal model.

Host rule: `run2.sh` and `run_g15_lake.sh` now take `flock
/tmp/aspis-r0-lean.lock` around the scoped job, so the host-wide one-job rule
is enforced by the launcher rather than by each worker's private lock. The
two recorded overlaps (3104/3229, 3108/3237) were each within their own caps
with zero swap; the affected results stand, and the condition cannot recur.


## Z3 continued after D9 — disclosed view and uniform affine laws (2026-10-09)

Fetched first and read D9 at the requested base
**`2f9124bb86757d5010eafc6dca41147f10b92021`**. All citations in this section
are to that git object. The shared branch continued advancing with soundness
work; this worker neither edited nor staged those sources or logs. The older
Z3 stop reports above are historical. D9 resolves the honest-H1 stop.

### Definitions and checked algebra

`HonestView.helper` is the source's weighted-reciprocal sum, using Lean's
field inverse, including `0⁻¹ = 0`. It is not the copy residual divided by
its H1 coefficient. Zero weights contribute zero. `prepare` installs this
helper in lane 26 after lambda/chi, before `applyAff` adds H1 padding. The
source `ActivePole` branch has no element in the ideal model. D9's **ZR1**
remains a refinement obligation: the real and ideal views may differ when
chi equals a nonzero-weight tuple; its symbolic bound is the tuple count
multiplied by `(1 + δQ) / P⁴`. This work proves neither that coupling nor its
probability bound and assigns no numerical error budget.

The statement is `Public K × CommitHandle`; `HonestProver` contains only an
instance type, its public projection, and its uninstantiated trace builder.
`HonestInstance = Instance × EligibleNoise`, with build applying
`applyEligible`. The unchanged MaskLayout split then applies the affine tape
(mask-only, G, H1 padding, D). The row-1023 semantic balancing reads only
semantic cells and eligible noise, never the affine tape. H1's original
oracle contribution is affine, including the copy-denominator slope proved
in ViewAffine; it is not claimed independent of H1 padding.

`View = Meta × Payload`. `metadata : Statement → Challenges → Meta`
(by fixing the public `outputs` adapter) contains the statement, all
challenges, nominal initial/C2 handles, positions and public auxiliary
outputs. Its type forbids instance/tape inputs. `Payload` is a finite
coordinate vector of field values: the mask claim, ten 28-coefficient
semantic polynomials, three MLE claim vectors, two OOD claim vectors,
inactive sum, seven opening-polynomial coefficients, 256 final coefficients,
and queried four-child symbols for each lane. Symbols at unqueried
positions are zero by `unqueried_zero`; that public zero extension supplies
a fixed vector space without disclosing the rest of a word. Full words are
only in `ProverOutput.W/C2`, never in the view. `messages` reconstructs the
32 scheduled message tags from the payload; `challengeAt` supplies the
25 semantic, two circle and five opening challenges (four scalars then the
query set), and the final opening response uses the query-gated symbols.

The payload's direct `run` applies the mask and evaluates its components.
`run_eq_payloadAffine` is proved from eight component lemmas. The semantic
oracle proof uses `ViewAffine.originalAt_affine` through
`originalAt_decomp`; all later sums, evaluations, interpolation, encoding,
relation polynomial and fold are affine/linear. `A` is the resulting
payload map's linear part over the **base subfield F**, and `b` is the actual
zero-tape payload. `view_affine` carries constant metadata alongside
`b + A r`. There is no affinity proof field in HonestProver. `MaskImage`
is D4′'s exact equal-range and zero-tape-displacement formula, over augmented
instances. No instance-independence of A is assumed or asserted.

`Completeness` is the builder obligation for `InputNoteExtracted`, literally
the relation selected by `sourceData.paymentWitness`. It is not a validity
premise, nor a claim of full verifier acceptance. `Obligations` contains
exactly `MaskImage ∧ Completeness`. The general distance statement is
retained, with perfect HVZK comparing laws of the complete pair for every
fixed challenge vector. The honest law uses the product of uniform eligible
noise and uniform affine tape; the simulator uses affine tape and a
classically chosen augmented instance for the public statement. No default
instance outside the language is required.

`AffineLaw.lean` is independent of the protocol. For abstract finite vector
spaces it identifies each nonempty affine fibre with `ker A`, translates the
coset to `range A`, and obtains the cardinality product through
`LinearMap.quotKerEquivRange`. `uniform_coset` and `equal_cosets_law` give the
uniform pushforward and equal-coset corollary, including different source
tape spaces. Additional generic lemmas carry constant metadata and
marginalise a product uniform tape when every fixed-noise conditional law
is equal. All cardinalities and finite sums stay symbolic on atomic types.

The old Z1 FS/ROM experiment is preserved under `ZkStatement.Z1`, including
its original `ZK_FS` definition. No ROM bridge, commitment assumption,
source refinement, or weakened FS claim is introduced. MaskImage itself
and completeness are still unproved obligations.

### Citation ledger

Abbreviations: **S** = `docs/research/v8-r0-sem-proof-20261008/lean/R0P/`;
**O** = `docs/research/v8-wide-reference-20261005/lean/R0/`.

| Definition or correspondence | Pinned source |
|---|---|
| Honest weighted reciprocals; source ActivePole | `crates/aspis-statement/src/logup.rs:192–224`; forest adapter `crates/aspis-statement/src/pool_v1/pair_forest_semantic_oracle.rs:168–179`; S/Copy.lean:454–463 (`copyRowsAt`). D9 specifies the ideal inverse at zero. |
| Adaptive helper and C2 order | `crates/aspis-prover/src/v6_onefold_prover.rs:1244–1257,1279–1312`: lambda/chi, helper error, padding, sum check, C2. D3 keeps D in the initial commitment. |
| Mask application / balancing | `crates/aspis-prover/src/state_only_hiding.rs:676–773`; eligibility `crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs:221–253`; H1 padding `state_only_hiding.rs:465–472`. Exact port and row-1023 boundary are in the preceding Z2/Z3 reports and unchanged MaskLayout. |
| Mask Boolean-sum claim and eta wrapper | `crates/aspis-prover/src/state_only_hiding.rs:845–883,900–952`; existing R0Z/MaskedProtocol wraps the R0 terminal, not a different historical terminal. |
| Semantic round polynomial construction | `crates/aspis-prover/src/state_only_zerocheck.rs:95–128`: 28 samples, remaining Boolean assignments, interpolation, challenge prefix update. This is a formula port; byte/error-path refinement is deferred. |
| Original terminal and H1 dependence | S/SemDecision.lean:43–49,73–80; S/Copy.lean:111–142,234–238; accepted R0Z/ViewAffine.originalAt_affine and terminalValue_eq_originalAt. |
| MLE claims and bit order | S/SemD3.lean:29–37; S/SemView.lean:36–57; O/OpeningDefinitions.lean:29–34. |
| OOD evaluation / linear interpolant | O/Chord.lean:35–36,51–64,83–99. |
| Opening virtual word, batching and weights | O/OpeningDefinitions.lean:36–40,53–69. `totalWeights` reads neither W nor the point-claim fields filled with zero in its public-data adapter. |
| Exact encoder linearity and injection | `docs/research/v8-wide-reference-20261005/lean/Wide/EncoderLinearity.lean:97–114,221–224`. `decode_encoded` proves that the proposed linear decoder is inverse on the encoded image. |
| Opening relation polynomial and final fold | O/RoundNormalization.lean:22–37; degree at most six at :43–53. |
| Outer message tags / schedule | `docs/research/v8-r0-close-20261007/lean/R0C/SemStatement.lean:18–33`; S/SemView.lean:30–34; accepted MaskedProtocol.schedule and D3. |
| Completeness relation | S/SemD3Glue.lean:88–111 (`paymentWitness := InputNoteExtracted`); S/Semantics.lean:77–81. |

### Lead decision needed — opening decoder stop

1. **Lead decision needed: ideal decoding off the encoder image.**
A review after the full view's local host checks identified a definition not
explicitly fixed by D4′/D4″/D9. The candidate `quotientLinear` forms the
pointwise chord quotient, then uses the exact encoder's linear left inverse.
The checked `decode_encoded` lemma fixes its value on encoded words, but the
linear extension off that image is a choice. All circle points are admitted
by the current `Challenges` type. For domain-intersecting secants, division
at zero need not produce an encoded word. The soundness model's
O/Chord.lean:28–33,112–124 supplies nonvanishing under distinct non-base
points, not for every point pair. D9 expressly fixes H1 at poles and does not
expressly select this opening extension.

The current view/statement checks below validate this **candidate**; they do
not settle that model choice. The lead has been asked whether to retain its
linear-left-inverse totalization. Dependent HVZK compilation stopped while
that required definition is unresolved. The uncompiled `Hvzk.lean` draft was
removed; no HVZK theorem is claimed. No good-challenge restriction or
conditioning has been added. The candidate sources are retained explicitly
for review and reuse if the lead adopts this extension; their compilation
is not acceptance of a new model decision. This stop follows the user's
“Stop on anything D4′/D4″/D9 doesn't determine” instruction, not an approval
rule or a resource failure.

### Host validation after D9

Host/workspace: `dombarker@100.108.41.90`,
`/home/dombarker/project-offloads/aspis-fs-generic-20261006`. The inspected
`run_g15_lake.sh` run2 adapter takes the shared
`flock /tmp/aspis-r0-lean.lock` around the scope. Every launch also had a
busy preflight; a busy 3114 preflight consumed no attempt/SHA receipt.
No private lock was used. The runner admitted 24 + 7 GiB beneath its
55 GiB reservation ceiling and used MemoryHigh=5G, MemoryMax=7G,
MemorySwapMax=0, TasksMax=128 and a 900-second timeout.
The command was `lake env lean -j1 -M7000 -DElab.async=false`.
Lean: 4.32.0 / `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.

Source revision for every row is **2f9124bb8 plus the exact source snapshot
SHA below**. Source/time/output/SHA receipts remain in host `evidence/`;
every snapshot was checked against its receipt. No package-wide replay was
run. Unchanged accepted dependencies were reused: MaskLayout 3108,
ViewAffine 3110 and StatisticalDistance 3000. Their local and host source
hashes match the earlier tables. SemD3Glue, SemDecision and SemD3 sources
also match both the host and the D9 base.

| Exact target | Attempt | Exit | Wall | Peak RSS (KiB) | Swap | Axioms / result |
|---|---:|---:|---:|---:|---:|---|
| `R0Z/HonestView.lean` | 3111 | 1 | 0:06.82 | 6,847,596 | 0 | Namespace/coercion and conditional goals; rejected. |
| `R0Z/HonestView.lean` | 3112 | 1 | 0:05.98 | 6,846,968 | 0 | Dot namespace / local reduction; rejected. |
| `R0Z/HonestView.lean` | 3113 | 0 | 0:06.24 | 6,867,748 | 0 | Initial four audits standard only; extended later. |
| `R0Z/ZkStatement.lean` | 3114 | 1 | 0:04.10 | 6,839,048 | 0 | Reserved public identifier / word namespace; rejected. |
| `R0Z/HonestView.lean` | 3115 | 1 | 0:07.36 | 7,016,880 | 0 | Evaluation homomorphism fields / decoder type inference; rejected. |
| `R0Z/HonestView.lean` | 3116 | 0 | 0:07.47 | 7,054,268 | 0 | Ten audits standard only; extended later. |
| `R0Z/ZkStatement.lean` | 3117 | 1 | 0:04.13 | 6,841,256 | 0 | Missing explicit augmented-instance binder; rejected. |
| `R0Z/ZkStatement.lean` | 3118 | 0 | 0:04.42 | 6,880,416 | 0 | 27 audits standard only; later switched to direct run. |
| `R0Z/AffineLaw.lean` | 3119 | 1 | 0:04.12 | 6,687,908 | 0 | Fibre membership hypothesis consumed by destructuring; rejected. |
| `R0Z/AffineLaw.lean` | 3120 | 0 | 0:04.06 | 6,720,292 | 0 | Six audits standard only, including equal_cosets_law. |
| `R0Z/HonestView.lean` | 3121 | 0 | 0:09.38 | 6,996,916 | 0 | 12 audits standard only; direct run bridge added later. |
| `R0Z/HonestView.lean` | 3122 | 1 | 0:08.83 | 7,012,328 | 0 | Aggregate simplification hit default recursion limit; rejected. |
| `R0Z/HonestView.lean` | 3123 | 1 | 0:08.90 | 7,013,724 | 0 | Same remaining aggregate reduction after opacity changes; rejected. |
| `R0Z/HonestView.lean` | 3124 | 1 | 0:09.85 | 7,013,896 | 0 | Four component changes still over-reduced; rejected. |
| `R0Z/HonestView.lean` | 3125 | 1 | 0:11.29 | 7,109,604 | 0 | One sum/coercion change still over-reduced; rejected. |
| `R0Z/HonestView.lean` | 3126 | 1 | 0:11.20 | 7,168,576 | 0 | Kernel memory guard on aggregate proof; rejected. |
| `R0Z/HonestView.lean` | 3127 | 0 | 0:11.52 | 7,039,316 | 0 | 13 audits standard only, including run_eq_payloadAffine. |
| `R0Z/ZkStatement.lean` | 3128 | 0 | 0:04.28 | 6,885,832 | 0 | 27 audits standard only, including view_affine; candidate definition review above. |

"Standard only" means a subset of `propext`, `Classical.choice`,
`Quot.sound`. The ZkStatement audit counts include 20 preserved historical
Z1 definitions and seven current declarations. Failed elaborations' audit
output is not accepted evidence; in particular 3126's kernel rejected the
aggregate bridge even though its elaboration reached the audit commands.

No cap or recursion/heartbeat limit was raised. After 3126 the replacement
was **eight separately kernel-checked component lemmas**, followed by a
small case-dispatch bridge, not an unchanged replay or larger cap. The
accepted 3127 source uses named affine-sum and component lemmas, with no
concrete row/tape/trace universe evaluation. Unused-section-variable warnings
are non-fatal. MaskLayout's previously accepted `applyAff_affine` audit was
reused rather than rerun unchanged.

| Attempt | Exact source SHA-256 |
|---|---|
| 3111 | `1f754df51376a0d17fd622abddba340ca3d81b1dda31e06ab261ffe9394b9a0d` |
| 3112 | `0def01c3fc2c387097524cc2f62a4bab18e9054e665a2e193bdb344e50f46042` |
| 3113 | `1db869ff5335149755b95788d5b106b2f3cfb5e5afc51d6d43d07e0043100e46` |
| 3114 | `ea29448370dc570feb4e9235d28b84bbe686131e6037a95661b9ca93df51853f` |
| 3115 | `a7c39086eaa0f3d8d07eb447dcaf172504c721fb60b478709e1938372248791e` |
| 3116 | `923e3c05fd4eca92d872cd07b34cfd83a856bfd91a467a67a1e7201233bc99c9` |
| 3117 | `24e1eeb16b4e797529c0a3b2816c9909b34f4fef32f814b78bb11aee96d500f3` |
| 3118 | `6a3b07fd7d77d805f98c6900cdd5cfc71a0ce4aafcce06622c2510ded3a3b360` |
| 3119 | `141051e376d8524d21df4451c5a9ceb3bd6521024a44e2a3ee83c8f5c12aeafb` |
| 3120 | `f680a0d4c8dab8f22f638c6aaad8c677a4ad973b327eb1908633e722a0707325` |
| 3121 | `5df882adefe627eccc47245c18605a2dd31510afe4d81532f08ddbd5662b6a68` |
| 3122 | `dda5805c51e7b9d1c295dedd903a0559d72624dadbab1f87bfef1fe35e5be699` |
| 3123 | `2c79d3d916bea54eaf678afb304f6a4fbe2d3b8d2f18349883dc4d6e1754083d` |
| 3124 | `0b6cb2bb2fefa5437287e64ee11cff6bd1fcf8f2166548fe4e435d3b3bdaf855` |
| 3125 | `aa0da2fb5a7e197ee47910161947262754fbdd250acd1f71f1de0b0b8b52218c` |
| 3126 | `509d6685e208553da68b677bbb4145095e4e21ba4f3ce0bbbc61b237abc28f3b` |
| 3127 | `566ba2db7fee7053b1a6562ee0ae6b09cbaf0fcfa8131dff81fc9eb77b5013c1` |
| 3128 | `b8a583bb76a1a7b8afcc6aaca68c5810cc2a1a89fd5075accb7bb5c14eb3fb84` |

The final current HonestView, ZkStatement and AffineLaw sources equal 3127,
3128 and 3120 byte-for-byte. `Hvzk.lean` was not host-compiled or retained.
The forbidden-declaration/evaluation/limit-override scan and scoped
`git diff --check` pass. Commit scope is HonestView, ZkStatement, AffineLaw
and this LOG only; no co-author trailer. The unchanged MaskLayout and
ViewAffine results are reused. No edits were made to Rust, the soundness
tree, or the historical extraction directory.

### Lead decision D10 — opening decoder off the encoder image (resolves the Z3 stop)

Retain the candidate: the ideal honest opening quotient is the pointwise
chord quotient followed by the exact encoder's **linear left inverse**
(`Wide/EncoderLinearity.lean:97–114,221–224`, `decode_encoded`). The linear
extension off the image is the ideal model's totalisation, in the same spirit
as D9: it keeps `view_affine` exact for every challenge vector and assigns a
value where the source has an abort. Where it is exercised: both circle
points are non-base-rational by the fallback design (`circleSample0/1_not_rational`),
so by `O/Chord.lean:28–33,112–124` the chord is nonvanishing on the domain
whenever `z0 ≠ z1`; the extension is therefore reached only on the event
`z1 = z0` (the soundness `z1Bad` fibre), of mass ≤ (1+δQ)/P⁴ under the ideal
samplers. Refinement obligation **ZR2**: the real prover's behaviour on
`z1 = z0` (abort or otherwise) differs from the ideal view on an event of at
most that mass; it joins ZR1 in the real-vs-ideal distance. Z3 should prove
the on-image lemma (`z0 ≠ z1 → quotient word ∈ encoder image`) so the
extension's irrelevance off that event is a theorem, not prose. No
good-challenge restriction or conditioning enters the ideal model.

## Z3 finish — D10 on-image decoder and conditional perfect HVZK (2026-10-09)

Fetched and used base **`fdd2a61c0a978f3c83284531ce361d3503dc35c5`**, including
D10. Work was confined to the privacy Lean tree and this LOG in the existing
`v8-reference` worktree. Concurrent Rust/measurement changes and the untracked
soundness refinement document were left to their owners. No Z4 rank/image
proof, builder completeness proof, source refinement, Rust build, or wallet/key
operation was attempted.

### D10 is now a theorem

`R0Z/KernelImage.lean` proves a generic rank-nullity fact: for maps `f,g : V →ₗ[k] W`
with `g` onto, an injection `ker f →ₗ[k] ker g` is onto. The proof compares
symbolic finranks; it does not compute any concrete dimension or enumerate a
finite type.

`R0Z/QuotientImage.lean` applies it to the exact message space. The two maps are
`(e1,e2)` and evaluation at the two circle endpoints. Interpolation makes the
latter onto. `Chord.product_eval` sends chord multiplication on `ker (e1,e2)`
into the evaluation kernel. `Chord.no_domain_zero` and exact encoder
injectivity make that restricted map injective. Consequently every message
minus its endpoint interpolant has an exact encoded chord quotient. This
supplies the image step in addition to nonvanishing; nonvanishing alone would
only justify pointwise division.

The checked declarations are:

- `quotient_mem_image_of_nonrational`: for arbitrary distinct non-base-rational
  endpoints, the honest `quotientWord` belongs to `Set.range exactInitialEncoder`.
- `quotient_mem_image`: for `z0 := circleSample0 s0`, `z1 := circleSample1 s1`,
  the only premise is `hz : z0 ≠ z1`. Nonrationality follows from the existing
  `circleSampleParameter0_not_rational` and `circleSampleParameter1_not_rational`
  applied to the sampler parameters (these are the source names at this pin).
- `quotientLinear_eq_decode` identifies the word with the input of the adopted
  linear left inverse. `quotientLinear_eq_of_encode_eq` and
  `quotientLinear_unique_preimage` show that its output agrees with the unique
  encoded preimage, using the accepted `decode_encoded` theorem.
- `quotient_off_image_only_eq` is the requested implication from an off-image
  quotient to `z1 = z0`. It asserts a necessary event, not that an off-image
  quotient must occur when the endpoints coincide.

No restriction was added to `Challenges`, `view`, or `MaskImage`. The generic
nonrational premises are discharged in the actual-sampler theorem, not inserted
into HVZK. No event probability or ZR2 source-distance bound is proved here.

### Perfect interactive HVZK, conditional on the unchanged MaskImage

`R0Z/Hvzk.lean` runs the accepted `AffineLaw.equal_laws_of_mask_image`
corollary of `equal_cosets_law` at each fixed augmented instance and challenge
vector. It carries the constant public metadata alongside the payload. The
simulator is the existing honest view on `Classical.choose hx`, where `hx`
provides an augmented instance for the public statement; no witness is supplied
to it by the real execution. `conditional_marginalisation` then uses
`AffineLaw.marginalisation` on the independent uniform eligible-noise tape.
Thus the checked theorem is exactly:

```lean
hvzk_perfect_of_maskImage (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) :
  MaskImage h B x → HVZK_perfect h B outputs x
```

`hvzk_zero_of_maskImage` also discharges the retained distance formulation at
zero. Completeness is a separate obligation, and no premise about it, map
independence, ROM security, or layout rank enters these proofs.

The final `#print R0Z.ZkStatement.MaskImage` in attempt **3143** reports the
following definition (implicit field/finite/algebra parameters omitted here):

```lean
MaskImage h B x :=
  ∀ (w w' : HonestInstance h F) (ch : Challenges K),
    «public» h w = x.1 → «public» h w' = x.1 →
      (A h B x w ch).range = (A h B x w' ch).range ∧
      b h B x w ch - b h B x w' ch ∈ (A h B x w ch).range
```

Here `HonestInstance h F = h.Instance × EligibleNoise K F`,
`EligibleNoise K F = EligibleCell → F`, and
`A h B x w ch : AffTape K F →ₗ[F] Payload K`.
Both eligible-noise components and every challenge vector are universally
quantified. This is the existing D4′/D4″ statement, unchanged and unproved;
Z4 is not started.

### FS interface stop — minimal proposed change, not adopted

The only existing `ZK_FS` is the preserved **`ZkStatement.Z1.ZK_FS`**, whose
`FSExperiments.real` and `.ideal` are arbitrary functions returning the old
31-round `ROMView`. It is not parameterized by the current prover/view types.
D5 fixes ideal tapes and defers seed/abort terms; it does not specify a ROM
compiler or a law relating either arbitrary function to the interactive
experiment. Even identical interactive views allow these functions to return
different constant observer-visible outcomes, with distinguishing advantage
one. Therefore `zkfs_of_hvzk_perfect` for that definition cannot follow from D5.

The minimal proposed current interface is to preserve Z1 as historical, keep
its Boolean-observer distinguishing-advantage expression and symbolic
`epsilon_fs`, and replace only its inputs/view with the current
`HonestProver`, chosen simulator, and full 32-round disclosed `View`. The ROM
view must still add the observer's own queries and complete 256-bit answers.
In schematic form, with the current `h,B,outputs,x` passed to the experiments:

```lean
ZK_FS ... x epsilon_fs :=
  ∀ hx adv w, h.public w = x.1 →
    |mean (fun r => if fs.observe adv (fs.real h B outputs adv x w r) then 1 else 0) -
     mean (fun r => if fs.observe adv
       (fs.ideal (simulator h B outputs x hx) adv x r) then 1 else 0)| ≤ epsilon_fs
```

An additional, separately proved **ROM reduction** is required. Its ideal
middle experiments must be the same randomized extension of the honest and
simulated interactive views, with the chosen instance-independent challenge
law and independent observer coins. HVZK supplies equality of those middle
laws. The real/ideal ROM games must then be connected to them with the actual
commitment/programming, seed, sampler-abort and source/refinement errors.
The eventual bridge would consequently have the explicit shape
`HVZK_perfect ... → ROMReduction ... epsilon_fs → ZK_FS ... epsilon_fs`.
This is a proposed obligation, not an assumed theorem or a replacement of FS
security by interactive equality. No epsilon term is assigned a value.

**Stop at the FS model decision:** the compiler, shared memoized oracle,
programming/conflict semantics, adversary/query bounds, and these reduction
proofs are not fixed by D5. The proposed interface has not been implemented;
`Z1.ZK_FS` is byte-for-byte unchanged. This uses the user's explicit
“minimal proposed change to ZK_FS with a stop” alternative. It does not block
the independently requested shared-mask cleanup below.

### Shared mask source and host evidence

After the first green quotient/HVZK checks, `R0Z/MaskedProtocol.lean` imports
`R0P.MaskValue`, deletes the eight duplicate mask definitions/structure, and
exports their existing names as aliases of `R0P.Mask`. The degree wrapper now
uses `R0P.Mask.maskValue_vdeg`. No consumer needed a source edit. The accepted
shared module is G25 attempt **3259**, source
`d87305635d05e315d4da28acdc334a0e1d057cee5bfbe7cc706cf02a3d1e2861`, matched
against both the local base source and the host. The changed module was checked
first, followed by one successful dependency-order pass through MaskLayout,
ViewAffine, HonestView, ZkStatement, QuotientImage and Hvzk (3138–3143).

Host: `dombarker@100.108.41.90`; pinned workspace
`/home/dombarker/project-offloads/aspis-fs-generic-20261006`.
Lean **4.32.0**, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
Mathlib **`81a5d257c8e410db227a6665ed08f64fea08e997`**.
Each command was `lake env lean -j1 -M7000 -DElab.async=false -R sources
-o objects2/<module>.olean sources/<module>.lean`, through the existing pinned
`evidence/run_g15_lake.py` adapter. The inspected run2 reservation adapter was
copied to `evidence/run_z3_finish_locked.sh`, retaining its resource settings;
its shared `flock /tmp/aspis-r0-lean.lock` was moved outside the wrapper so it
covered source installation, snapshot creation, and compilation together.
Attempts refuse to overwrite an existing SHA receipt. Every scope used
MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128, timeout 900 s and a
unique `aspis-z3-<attempt>` unit. Every admission reported **24 + 7 GiB** below
the **55 GiB** reservation ceiling. No cap, recursion, or heartbeat limit was
raised. There was no cold dependency build, generated certificate, package-wide
or frozen-manifest replay, arithmetic gate, or unrelated regression suite.

Source revision for every row below is **fdd2a61c0 plus the exact source
snapshot SHA-256 in the second table**, with 3137's shared-mask import change
in the dependency closure for 3138–3143. The concurrently advancing Rust HEAD
does not change this source pin. The unchanged dependency sources were checked
against the base. Host copies of CircleSampler, SemD3Glue, MaskValue,
EncoderLinearity, AffineLaw and StatisticalDistance match those sources;
the already configured R0 cache was reused and its three chord object hashes
inventoried. No inherited cache was rebuilt merely to check a downstream lemma.

Raw host `evidence/source-N.lean`, `sha-N.txt`, `out-N.log` and `time-N.log`
are retained. Hash-verified local copies and the dependency inventory are in
`/tmp/aspis-z3-finish/evidence/`; raw evidence is excluded from commits, as in
the preceding runs. Every final local source equals its accepted snapshot.

“Standard” below means a subset of `propext`, `Classical.choice`, `Quot.sound`.
Failed elaborations' audit output is rejected, even if individual declarations
printed standard axioms. All final requested theorem audits show exactly the
three standard axioms and no `sorryAx`.

| Attempt | Exact target | Exit | Wall | Peak RSS (KiB) | Swap | Result / axioms |
|---|---|---:|---:|---:|---:|---|
| 3129 | `R0Z/KernelImage.lean` | 1 | 0:02.82 | 6,677,712 | 0 | Rejected: incorrect finrank theorem namespace. |
| 3130 | `R0Z/KernelImage.lean` | 0 | 0:02.93 | 6,713,864 | 0 | Standard; generic kernel lemma. |
| 3131 | `R0Z/QuotientImage.lean` | 1 | 0:03.56 | 6,795,268 | 0 | Rejected: product coercions and excessive definitional reduction. |
| 3132 | `R0Z/QuotientImage.lean` | 1 | 0:03.80 | 6,792,412 | 0 | Rejected: endpoint simplification and unresolved chord coefficient. |
| 3133 | `R0Z/QuotientImage.lean` | 0 | 0:04.08 | 6,825,448 | 0 | Standard; four quotient audits, before shared-mask refactor. |
| 3134 | `R0Z/Hvzk.lean` | 0 | 0:03.33 | 6,832,960 | 0 | Standard; four HVZK audits, before shared-mask refactor. |
| 3135 | `R0Z/MaskedProtocol.lean` | 1 | 0:03.04 | 6,783,976 | 0 | Rejected: documentation comment immediately before export. |
| 3136 | `R0Z/MaskLayout.lean` | 0 | 0:08.32 | 6,840,032 | 0 | Standard output, but premature dependent run; not accepted as post-refactor evidence. |
| 3137 | `R0Z/MaskedProtocol.lean` | 0 | 0:03.15 | 6,819,204 | 0 | Standard; shared-mask import/aliases and degree wrapper. |
| 3138 | `R0Z/MaskLayout.lean` | 0 | 0:08.54 | 6,840,028 | 0 | Standard; final MaskLayout dependent check. |
| 3139 | `R0Z/ViewAffine.lean` | 0 | 0:03.18 | 6,820,548 | 0 | Standard; final ViewAffine dependent check. |
| 3140 | `R0Z/HonestView.lean` | 0 | 0:13.37 | 7,037,472 | 0 | Standard; final HonestView dependent check. |
| 3141 | `R0Z/ZkStatement.lean` | 0 | 0:04.74 | 6,886,148 | 0 | Standard; final ZkStatement dependent check. |
| 3142 | `R0Z/QuotientImage.lean` | 0 | 0:04.25 | 6,824,964 | 0 | Standard; final four quotient audits. |
| 3143 | `R0Z/Hvzk.lean` | 0 | 0:03.26 | 6,833,488 | 0 | Standard; final four HVZK audits and printed MaskImage. |

The 3131 recursion-depth failure was replaced by explicit product projection,
opaque encoder/interpolant boundaries and explicit subtype projections; no
limit was increased. The later coefficient was named explicitly, and endpoint
conditionals were simplified directly. 3135 was a parser-only failure; 3136
was inadvertently launched before reading that failure, so it is not counted
as final dependent validation. The local orchestrator now propagates the
recorded inner exit status. After the corrected 3137 predecessor was green,
3138–3143 completed once in dependency order. Nonfatal warnings remain in
unchanged MaskLayout/HonestView; both new final proof modules are warning-free.

| Attempt | Exact source SHA-256 |
|---|---|
| 3129 | `29c61406f4ff00565558ad9b6ca0e2c0a7ed95f0da5b0c2eda94e0c6425bb8c6` |
| 3130 | `60a7df59579170c177c636feac85be504457a4b165a8a8c489014a24d1ac6722` |
| 3131 | `4b150a5d490d0631f9891271ee8d68489ae65e235f7e8a6a05bddd7c7a6f5f68` |
| 3132 | `983c3abf21e29b728dc3fb71147b4a3b7e12736c3b7aadbcab9ee7367918f894` |
| 3133 | `a2c303da28842f0b20c4b51372a21fbe7a14b859fddb34957282badb88ff84cb` |
| 3134 | `c955ed87adf647cc5fe94ff577632f5f9534555d5566dcedab2e6f5b101b97d4` |
| 3135 | `07dace2242446610a921d278b468ac8d0e58aa5f181e3aee1d7458d389457917` |
| 3136 | `4f0615a66f8abe90b80d1cdff56961356cff13628c85dbd3456f43d9f425b43a` |
| 3137 | `5efc4563c936eb7d7a4da9e70a1d2782e759868c1709fc477c3580c03914a4a8` |
| 3138 | `4f0615a66f8abe90b80d1cdff56961356cff13628c85dbd3456f43d9f425b43a` |
| 3139 | `7719f782cf4a3326f27373d59f378d130e035f3698c6ea0d3379da69fabbe33a` |
| 3140 | `566ba2db7fee7053b1a6562ee0ae6b09cbaf0fcfa8131dff81fc9eb77b5013c1` |
| 3141 | `b8a583bb76a1a7b8afcc6aaca68c5810cc2a1a89fd5075accb7bb5c14eb3fb84` |
| 3142 | `c380622230deaef7db8769351ccf8a44989c36b13895d71169f314fc49dc08c9` |
| 3143 | `5c8c2abc96eb2e2a7049e2cf0d947856076667dbc7ab00de2758227c0ff904f5` |

The final forbidden-declaration/evaluation/limit-override scan and scoped
`git diff --check` pass. Commit scope is KernelImage, QuotientImage, Hvzk,
MaskedProtocol and this LOG only; no co-author trailer. Z3's conditional
interactive theorem and D10 image lemma are complete. The FS decision above,
MaskImage itself (Z4), builder completeness, and source/ROM refinement remain
open. Report and stop.

### Lead decision D11 — MaskImage restated (corrects D4″); ZK_FS interface adopted

Z3 is accepted as proved. The compiled `MaskImage` (eligible noise `e` in the
instance, D4″) is however not provable for the layout: `b(w,e) − b(w',e')`
contains the C1 semantic columns' opened symbols and point claims, which the
affine tape never touches. The eligible noise is what hides those; it belongs
in the tape. Its nonlinear entry into the original's round polynomials is
absorbed by the mask's linear part. Statement:

- `HonestInstance := Instance` (no noise). Tape `T := AffTape ⊕ EligibleNoise`,
  uniform (D5). `view x w ch (r,e) = c + A (r,e) + (g w e, 0)` where
  `c := view x w ch (0,0)`, `A : T →ₗ Payload` is the linear part
  (every component is affine in `(r,e)` except the original's round
  polynomials, which are affine in `r` and polynomial in `e`; `g w e` is that
  remainder, in the round-polynomial component only, `g w 0 = 0`).
- `MaskImage x :=`
  (i) `∀ w e, public w = x → (g w e, 0) ∈ range (A ∘ inl)`
      (the mask-only/G/H1/D part alone absorbs the remainder), and
  (ii) `∀ w w', public w = x → public w' = x → c w − c w' ∈ range A`.
- Theorem (Z3b): `MaskImage x → HVZK_perfect x`. For fixed `e`, `r ↦ view`
  is uniform on `c + A(0,e) + range(A∘inl)` by (i); mixing over uniform `e`
  gives the pushforward of uniform `(r,e)` under `c + A`, uniform on
  `c + range A` (AffineLaw); (ii) makes it instance-independent.
- Z4 then proves (i) and (ii) for the layout. (i) is the rank statement the
  Rust q29 gate measures; (ii) is the hiding of C1 openings/claims by the
  eligible cells (an encoder-restriction surjectivity) plus the mask lanes.

ZK_FS: the Z3 proposal is adopted as the definition — `ZK_FS` over the
current `HonestProver`, simulator and 32-round `View`, Boolean observer,
symbolic `ε_fs`. The ROM reduction `HVZK_perfect → ROMReduction ε_fs →
ZK_FS ε_fs` is obligation **ZF1**, deferred until after Z4; no value is
assigned to `ε_fs` and `Z1.ZK_FS` stays as history.

## Z3b — joint-tape experiment and FS interface; D11 mixed-H1 stop (2026-10-09)

Fetched base **`41d8f6120993b7d13a43ae4785b48059c1c21a02`** and read D11.
The accepted Z3 modules are retained. The old `ZkStatement.MaskImage`
definition is unchanged except for a docstring marking it superseded.
`JointView.lean` installs `HonestInstance := h.Instance`, the joint uniform
tape `AffTape K F × EligibleNoise K F`, the actual honest view and its
zero-tape payload `c`, and a simulator using a classically chosen instance
while sampling both tapes. The product represents the binary vector-space
direct sum: both components are sampled, rather than choosing one summand.
`view_eq_z3` proves exact equality with the accepted view at `(w,e),r`.

**Items 1–2 stop before defining the claimed linear A and eligible-only g.**
The source has a mixed H1-padding/eligible-noise term. Being affine in `r`
for each fixed `e` does not imply that its nonlinear remainder is a function
of `e` alone. No assumed decomposition, unproved linear map, replacement
honest view, or altered MaskImage was installed. The requested
`hvzk_perfect_of_maskImage'` and the Z4 maps derived from that A are therefore
not claimed. The independent FS interface work is complete below.

### Sparse mixed-term obstruction to D11 as written

D11 asks for `payload(r,e) = c + A(r,e) + (g(e),0)`. Any such expression
satisfies the necessary identity

```text
payload(r,e) - payload(0,e) - payload(r,0) + payload(0,0) = 0.
```

`D11Obstruction.separated_mixed_difference` proves this for arbitrary modules
and a linear A. The condition `g(0)=0` is not even needed for this identity.
The source-level sparse instantiation below gives a nonzero mixed difference
in a linear observable of the final semantic round-polynomial coefficients.
This is an obstruction to the proposed decomposition, not a privacy attack.

1. Let `s : F` be the eligible mask at **semantic column 0, row 13**, with all
   other eligible coordinates zero. It changes that trace cell by `s` and
   its balancing cell, row 1023, by `-s`.
2. Let `h : F` be the **first limb of H1 padding at row 13**, with all other
   affine coordinates zero. H1 padding changes row 13 by `h` and its balancing
   row 0 by `-h`. Rows 0, 13 and 1023 are copy-inactive; row 12 is active.
3. Choose the MSB-first evaluation point
   `a = (0,0,0,0,0,0,1,1,0,2)` and zerocheck point
   `zc = (0,0,0,0,0,0,1,1,0,0)` (Boolean row 12). The MLE support at `a` is
   exactly rows **12 and 13**, with weights **-1 and 2**. Thus the C1 opening
   changes by `2*s` and the H1 opening changes by `2*h`. Both balancing rows
   have zero evaluation weight. These are ten-factor sparse weight identities,
   not an expansion or evaluation of a 1024-row matrix.
4. Set `lambda = chi = theta = eta = 1`, `mu = 0`. The only copy endpoint at
   either row in that support is the producer at row 12, slot 0, pattern 1,
   tag **1124073480**, weight 1. Pattern 1 reads columns 0–7 with coefficient
   one at lambda 1. The producer value at this point is
   `-(tag + offset + 2*s)`, its weight is `-1`, and every other producer or
   consumer slot has zero value and weight. `offset` contains the fixed
   trace contributions. The equality and active selectors are both `-1`,
   whose product is one.
5. The unpadded helper at row 12 reads the unchanged Boolean-row semantic
   cells; row 13 has no endpoints and its weighted reciprocal helper is zero.
   Hence the base H1 opening, denoted `H`, is fixed as s varies. The actual
   copy residual at `a` is consequently

   ```text
   (1 + tag + offset + 2*s) * (H + 2*h) + 1.
   ```

   Its rectangular difference in s and h is **`4*s*h`**. All other terminal
   lanes and the mask term are independent of H1 padding; their rectangular
   differences are zero. The mu terms vanish by the chosen challenge.
6. Fix the first nine alpha challenges to the first nine coordinates of `a`.
   The last round polynomial has no remaining Boolean tail, and its
   interpolation sample at **X = 2** is exactly this terminal value. Evaluation
   at 2 is a linear function of its 28 disclosed coefficients. Taking
   `s = h = 1` therefore yields mixed difference **4**, nonzero in M31 and
   its extension. This contradicts the necessary zero identity above.

**Proof boundary:** `sparse_copy_mixed_difference` and
`sparse_copy_not_separated` are host-compiled symbolic lemmas for the displayed
four-slot copy row. The latter takes the explicit premise `(4 : K) ≠ 0`.
The full sparse-support/registry/interpolation instantiation above is a
source-level algebraic audit, not a newly claimed kernel-checked theorem about
`HonestView.run`. The source inventory checks the exact endpoint and active
bits; it performs no field, encoder, matrix, or rank computation.

Source citations at the base:
`MaskLayout.lean` (`eligible`, `balance`, `h1Padding`, `applyEligible`,
`applyAff`); `HonestView.lean` (`helper`, `prepare`, `original`, `roundPoly`,
`run`); `R0P/Copy.lean` (`copyResidual`, `copyEvaluateWithSelectors`,
`copyRowsAt`); `R0P/CopyConstants.lean:150–151` (rows 11 and 12 endpoints),
`:30–31` (active masks), `copyPattern1`; `R0P/SemDecision.lean`
(`laneAt`, `eqValue`, `activeAt`, `terminalValue`); and
`R0P/SemDeg.lean` (`selAt_eq_bitWeight`, `g2High_selAt`, `g2Low_selAt`). The Rust
row-12 record is `pair_forest_copy_terminal_constants.rs:36`. These source
formulas are the same ones cited in the accepted Z3 H1-slope analysis.

A clarification was requested while independent FS work continued. A possible
repair is to let the round remainder depend on eligible noise **and H1
padding**, then absorb it using independent mask-only/G randomness (retaining
all tape coordinates). That requires a different conditional translation
argument; merely changing `g(e)` to an arbitrary `g(r,e)` would not justify
uniformity because the translation could depend on the same randomness used
to absorb it. No repair was adopted without a lead decision. Any repaired
argument must also prove a common affine image across instances; the old
`ViewAffine` theorem does not assert an instance-independent H1 slope.

### Adopted ZK_FS definition and explicit ZF1 composition

`FsStatement.lean` installs the current `ROMView`, `FSExperiments` and
`ZK_FS` in namespace `R0Z.FsStatement`. The view contains the current complete
32-round disclosed view and the observer's own queries with full 32-byte
answers. The advantage is the absolute difference of the real and ideal
Boolean-observer means, with symbolic `epsilon_fs`. The real experiment takes
the current `HonestProver`, basis, public output projection and instance; the
ideal experiment takes the current chosen-instance simulator. `Z1.ZK_FS`
remains historical and unchanged.

`ROMReduction ... epsilon_fs : Prop` requires an explicit common randomized
extension, with finite nonempty coins independent of the joint prover tape.
Its challenge draw and extension cannot read the honest instance. It also
requires nonnegative comparison errors `epsilon_real`, `epsilon_ideal`,
whose sum is at most `epsilon_fs`, and proofs of both real-game comparison
bounds. These are the places where commitment/programming conflicts, seed
replacement, sampler abort and source/refinement errors must be justified.
No reduction certificate, oracle semantics, query bound, or error value is
supplied by this module.

`LawTransport.lean` proves equal expectations under equal finite laws for
arbitrary output types, and product-coin marginalisation. They give
`middle_means_eq` from the current fixed-challenge HVZK statement. The triangle
inequality then proves the requested purely compositional theorem:

```lean
R0Z.FsStatement.zkfs_of_hvzk_perfect ... :
  R0Z.JointView.HVZK_perfect h B outputs x →
  ROMReduction h B outputs fs x epsilon_fs →
  ZK_FS h B outputs fs x epsilon_fs
```

ZF1's substantive game/reduction proof remains open. No implication from D5
alone, no efficiency property, and no actual FS privacy result is asserted.

### Z4 coordinate inventory; map statements blocked by the D11 decomposition

The following counts inventory the current types/layout, not their ranks.
The local script `/tmp/aspis-z3b/layout_inventory.py` and its source-hashed
JSON result are retained in `/tmp/aspis-z3b/evidence/layout-inventory.json`.
It only counts the natural-number eligibility predicate and literal active
bits. No concrete linear matrix was constructed or evaluated, and no Lean
cardinality or surjectivity proof is claimed.

| Tape block | Raw independent F coordinates |
|---|---:|
| Ten mask-only columns | 10 × 1024 = 10,240 |
| G, H1 padding, D (four limbs each) | 3 × 1024 × 4 = 12,288 |
| AffTape total | 22,528 |
| EligibleNoise | 3,803 |
| Joint tape total | 26,331 |

Eligible-cell counts for columns 0–15 are
`222, 222, 223, 224, 224, 224, 224, 224, 224, 248, 249, 259, 259, 259, 259, 259`.
The copy registry has 214 active and 810 inactive rows. Overwritten balance
samples and unused H1 active-row samples are retained in the raw tape; these
raw dimensions must not be read as the ranks of its image.

Writing `q := ch.queries.card`, the disclosed field-coordinate inventory is:

| Field payload projection | K slots | At q = 22 |
|---|---:|---:|
| Semantic round-polynomial coefficients | 10 × 28 | 280 |
| Semantic C1 columns' three point claims, two OOD values, and opened symbols | 16 × (5 + 4q) | 1,488 |
| Remaining 13 columns' direct claims and opened symbols | 13 × (5 + 4q) | 1,209 |
| Mask-sum, inactive sum, seven opening coefficients, 256 final coefficients | 1 + 1 + 7 + 256 | 265 |
| Total | 690 + 116q | 3,242 |

Thus the complement of semantic C1 claims/openings has `610 + 52q` K slots,
or 1,754 at q22, including the 280 round coefficients. Metadata carries no
vector-space dimension. To compare with F-coordinate tapes, ambient K-slot
counts must be multiplied by `[K:F]`; `PackBasis F` alone does not identify
all of K with four F coordinates. These are ambient counts and do not remove
sumcheck/encoder consistency relations or subfield restrictions. Surjectivity
onto an unrestricted ambient array must not be substituted for surjectivity
onto the required displacement subspace.

The current `Challenges` type admits arbitrary query sets. The q22 column is
an explicitly labelled specialization, not an added premise or a silent
restriction of `∀ ch`. The fixed, zero-extended Payload type itself has
30,409,394 K coordinates; only the queried positions are used in the counts
above.

**No A-composed Z4 maps or closing surjectivity lemmas were installed:** doing
so as though D11's A existed would conceal the decomposition obstruction.
The next action is the lead's remainder/absorption decision, followed by those
map definitions and goal statements. No Z4 rank argument has begun.

### Host validation

Host/workspace and toolchain are unchanged from Z3: `dombarker@100.108.41.90`,
`/home/dombarker/project-offloads/aspis-fs-generic-20261006`, Lean 4.32.0
(`8c9756b28d64dab099da31a4c09229a9e6a2ef35`), pinned Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`. The existing shared-lock adapter
and Python Lake launcher were reread before use. Each attempt used the common
`/tmp/aspis-r0-lean.lock` across source installation and compile, one Lean
process, MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128, 900 s timeout,
and `lake env lean -j1 -M7000 -DElab.async=false`. Each admission was 24+7 GiB
under the 55 GiB reservation ceiling. No resource or elaboration limit was
raised. No package-wide replay, cold build, finite-field gate, or concrete rank
computation ran.

Source revision for every receipt is **41d8f6120 plus its exact source snapshot
SHA below**. Attempts 3151–3153 reuse the docstring-only ZkStatement change
compiled in 3149. Unchanged accepted dependencies are reused. Source, SHA,
output and GNU-time receipts remain on the host and in
`/tmp/aspis-z3b/evidence/`; none are added to the commit. Every final source was
matched byte-for-byte to its accepted snapshot. “Standard” denotes only
`propext`, `Classical.choice`, `Quot.sound` (or a subset). Failed audit outputs
are rejected, even when other declarations in that file printed successfully.

| Attempt | Exact target | Exit | Wall | Peak RSS (KiB) | Swap | Result / axioms |
|---|---|---:|---:|---:|---:|---|
| 3144 | `R0Z/JointView.lean` | 1 | 0:02.74 | 6,794,840 | 0 | Rejected: missing classical decidability for the eligible-cell finite type. |
| 3145 | `R0Z/LawTransport.lean` | 0 | 0:02.80 | 6,713,784 | 0 | Standard; expectation transport and product means. |
| 3146 | `R0Z/JointView.lean` | 0 | 0:02.83 | 6,828,768 | 0 | Standard; exact joint-view bridge and new HVZK definition. |
| 3147 | `R0Z/FsStatement.lean` | 0 | 0:03.06 | 6,844,508 | 0 | Standard; FS definition, reduction obligation, composition theorem. |
| 3148 | `R0Z/D11Obstruction.lean` | 1 | 0:07.94 | 6,792,192 | 0 | Rejected: four-slot vector projections not fully simplified. |
| 3149 | `R0Z/ZkStatement.lean` | 0 | 0:04.31 | 6,886,748 | 0 | Standard; old MaskImage docstring marked superseded, definitions unchanged. |
| 3150 | `R0Z/D11Obstruction.lean` | 0 | 0:03.23 | 6,819,492 | 0 | propext/Quot.sound only; sparse mixed-term algebra. |
| 3151 | `R0Z/Hvzk.lean` | 0 | 0:03.10 | 6,833,340 | 0 | Standard; preserved Z3 theorem after imported docstring change. |
| 3152 | `R0Z/JointView.lean` | 0 | 0:02.88 | 6,828,124 | 0 | Standard; final joint-view dependent check. |
| 3153 | `R0Z/FsStatement.lean` | 0 | 0:03.12 | 6,844,096 | 0 | Standard; final FS dependent check. |

| Attempt | Exact source SHA-256 |
|---|---|
| 3144 | `15818c1465abc7fbe9fea490e5335d8769e2e0118d530e2b175d4897a1095272` |
| 3145 | `dcb5c119d30f86bf9479db73924cc466fc67348dcd4093f92094f85050711a90` |
| 3146 | `a46749539ce3237da99950ad08ced4df72d8433c5e6f327e21850d08f1d07182` |
| 3147 | `3c42085757381a4bb065615c14f40cc989c5c52e2e60e79486508713ed311cdf` |
| 3148 | `80128f23781709fc0a284051fa0aa1fba80658b0d08e12a8c46f167ba124fc83` |
| 3149 | `bb50e02cee78677adbe9fc88cf2f6f40b15a2385d445c62230b3ec2950da6d39` |
| 3150 | `426b645e41e0ce779a6194213b5f52707edd2108c3730f7c7a6df0c62819ca14` |
| 3151 | `5c8c2abc96eb2e2a7049e2cf0d947856076667dbc7ab00de2758227c0ff904f5` |
| 3152 | `a46749539ce3237da99950ad08ced4df72d8433c5e6f327e21850d08f1d07182` |
| 3153 | `3c42085757381a4bb065615c14f40cc989c5c52e2e60e79486508713ed311cdf` |

The final scoped diff/forbidden-declaration/evaluation/limit-override checks
pass. The only simplification in the new copy obstruction expands a fixed
four-slot row and a ring identity, never the large registry or a concrete
recurrence. No new file contains a sorry, axiom, unsafe declaration, or native
evaluation. Commit scope is the four new modules, the old MaskImage docstring,
and this LOG. Concurrent Rust/spec work is untouched; no wallet operation,
co-author trailer, or rank-proof claim. Z3b stops at the D11 correction above.

### Lead decision D12 — remainder depends on all multiplied coordinates (corrects D11)

Z3b's finding is accepted: the copy residual multiplies H1 by trace cells, so
with both in the tape the original's last round polynomial has a bilinear
term in (H1 padding, eligible noise); D11's `g w e` was too narrow. Fix:

- Partition the tape `T = M ⊕ N`. `M` ("pure-linear") are the coordinates
  that no payload component ever multiplies by another tape coordinate or by
  the trace: the ten mask-only columns and D; G belongs to `M` iff the
  original terminal never multiplies lane 27 by a tape-dependent value (Z3b
  decides from the algebra and records it); H1 padding and the eligible
  noise are in `N`.
- `view x w ch (m,n) = c + A (m,n) + (g w n, 0)` with `c := view (0,0)`,
  `A` linear, `g w n` the remainder in the round-polynomial component only,
  `g w 0 = 0`; it may be any polynomial in `n`.
- `MaskImage x :=`
  (i) `∀ w n, public w = x → (g w n, 0) ∈ range (A ∘ inl_M)`;
  (ii) `∀ w w', … → c w − c w' ∈ range A`.
- Theorem: `MaskImage x → HVZK_perfect x`, same proof: for fixed `n`,
  `m ↦ view` is uniform on `c + A(0,n) + range(A∘inl_M)` by (i); the
  mixture over uniform `n` is the pushforward of uniform `(m,n)` under
  `c + A`, uniform on `c + range A`; (ii) gives instance-independence.
  (i) is still the rank statement of the Rust gate: the mask-only columns'
  round-polynomial image must cover the round-polynomial displacement space.

## Z3b continued — D12 partition, decomposition and perfect HVZK (2026-10-09)

Fetched and read base **`01920c65827981a56ef10b7af3e3e7fdaae6fef4`**.
`a4399872c9d4c5d5e26dc86b86ee56096f840937` was already an ancestor of
`origin/v8-reference`, so its requested push was already satisfied. Work
remained in this privacy directory in `.worktrees/ZK-v8-reference`.
The concurrent Rust SPEC commit `783aa3f97` did not change these proof inputs.
Old Z3/D11 results and the current `JointView`/`FsStatement` experiments are
preserved. The new current conditional theorem is in **`R0Z.D12`**.

### Partition and G verdict

**G belongs to M.** At the requested base,
`R0P/SemDecision.lean:74–80` constructs `terminalValue` solely from claims in
semantic columns 0–15 and the H1 claim at lane 26. Its `laneAt` function
(`:45–49`) takes exactly those semantic openings, H1 and selectors. The
29 theta lanes here are residual lanes, not 29 trace-column reads. In
particular there is no read of G/lane 27 in the original terminal.
`R0P/Copy.lean:111–123,126–142` multiplies H1 by products of semantic
copy-denominator values, explaining D11's H1/noise mixed term; it does not
multiply G. `R0P/MaskValue.lean:42–56` reads G only as
`(1 + maskLinear 16 alpha ^ 26) * G(alpha)`. That coefficient depends on
fixed alpha, never on the instance or tape. The ten mask-only columns also
have point-only coefficients; D is absent from `maskValue`. The remaining
observations in `HonestView.run` are the already ported linear claims,
encoding, quotient, relation and folding maps.

`Partition.lean` therefore uses:

- M = ten mask-only column tapes, G limbs and D limbs;
- N = H1-padding limbs and eligible semantic-cell noise;
- T = M × N, representing the binary vector-space direct sum.

`Partition.equiv` is a proved linear equivalence to the **unchanged**
`JointView.Tape = AffTape × EligibleNoise`. Every raw input coordinate,
including overwritten balance samples and unused H1 active-row samples,
is retained. `pureTrace_fixed` proves that changing M leaves all semantic
columns and H1 untouched. `PayloadSplit.terminal_add_pure` applies that
fact to the actual terminal. `D12.M_pure` proves for all w, n and m:

```text
payload(w,(m,n)) = payload(w,(0,n)) + (A ∘ inl_M)(m).
```

A depends only on the basis and fixed challenges. Thus the slope of every
payload component is independent of both n and w, including all round
coefficients. Public metadata is constant in both tapes and the instance.
These are unconditional algebraic theorems, not MaskImage premises.

### Joint affinity and the supported remainder

The other necessary source fact is now also proved:
`HelperInvariant.helper_eligible` says the unpadded honest H1 helper is
unchanged by **every** eligible-noise tape. `protected_registry` verifies
that both endpoints of every literal copy link read only non-eligible
cells and never row 1023, the overwritten semantic balance row. The
certificate consists of bounded checks of at most four existing registry
records per declaration, examining only natural-number rows and pattern
limbs. A first four-record chunk was checked before the complete set.
The endpoint-tuple equality, row-sum equality and reciprocal-helper equality
are then symbolic proofs; no field or trace universe is enumerated.
The equality includes the D9 total inverse at poles without a new condition.

`JointTrace.actual_affine` proves the complete prepared/masked trace is its
zero-tape trace plus one common F-linear map of T. This uses the helper
invariance above, linear balancing, and the accepted `applyAff` identity.
`PayloadSplit.run_split` proves equality to the existing honest payload:

```text
run = L(actual trace) + O(actual trace),
```

where L contains every linear mask observation (mask-sum and round masks
included) and all other linear observations; O contains precisely eta times
the original terminal's round-polynomial coefficients, zero elsewhere.
The exact interpolation and ported `HonestView.run` are retained.

The decomposition is made explicit, with no choice of a witness-dependent
slope: **A = L ∘ tapeLinear**; **c = JointView.c**; **g(w,n)** is the change
in O's round arrays between `(0,n)` and `(0,0)`. This choice assigns the
original terminal's entire change, including any terms linear in n, to g.
D12 does not require g to have zero derivative or to be homogeneous of degree
at least two. `g_zero` proves g(w,0)=0. `D12.decomposition` proves:

```text
payload(w,(m,n)) = c(w) + A(m,n) + roundInclusion(g(w,n)).
```

`roundInclusion` is exactly `(g,0)` in D12. In particular,
`other_components_affine` proves all non-round components jointly affine in
(m,n) with the same common A. This includes H1 claims/openings, the mask-sum,
inactive sum, and the opening/final polynomial coefficients. The view's
metadata remains the existing constant `ZkStatement.metadata outputs x ch`;
it is not assigned an artificial vector-space structure.

### D12 MaskImage and HVZK

`D12.MaskImage` is D12 verbatim, with challenges universally quantified and
`h.public w = x.1` following the existing ideal-handle convention:

```text
(i)  ∀ ch w n, public w = x → (g(w,n),0) ∈ range(A ∘ inl_M)
(ii) ∀ ch w w', public w = x → public w' = x → c(w)-c(w') ∈ range A.
```

There is no extra affinity, helper, equality-of-ranges, good-challenge,
completeness or rank assumption. `AbsorptionLaw.fixed_n` invokes the accepted
finite affine-coset theorem with clause (i), so each conditional law is that
of `c + A(0,n) + (A ∘ inl_M)(m)`. `mixture` averages over independent uniform
n to obtain exactly the pushforward of uniform `(m,n)` under `c + A`.
`uniform_coset` identifies its law as uniform on `c + range A`.
Clause (ii) makes these cosets equal across honest instances. The proved
coordinate equivalence transports this law to the original joint tape and
the constant metadata pair is restored. The resulting theorem is:

```lean
R0Z.D12.hvzk_perfect_of_maskImage :
  D12.MaskImage h B x → JointView.HVZK_perfect h B outputs x
```

The conclusion is the existing experiment and chosen-instance simulator,
not a new or conditioned privacy notion. `MaskImage` itself, Z4, builder
completeness, ZF1 and source/ROM refinement remain open.

### Z4 opening move — maps, lemma targets and dimensions

`Z4Maps.roundMaskMap` is the round-polynomial projection of `A ∘ inl_M`.
Because (i) specifies zero in **all other** components, `silentMasks` is the
kernel of its non-round observation and `silentRoundMaskMap` restricts the
round map to that kernel. The first surjectivity-type target is:

```text
∀ ch w n, public w = x →
  ∃ m ∈ silentMasks, silentRoundMaskMap(m) = g(w,n).
```

`Z4Maps.c1Map` is A projected to semantic C1 columns 0–15: three point
claims, two OOD claims, and query-gated opened symbols. Its target is:

```text
∀ ch w w', public w = x → public w' = x →
  c1Projection(c(w)-c(w')) ∈ range c1Map.
```

These are named **Prop definitions** `roundMask_surjectivity` and
`c1_surjectivity`, exposing the two future lemma statements without asserting
or assuming their proofs. The C1 statement is the encoder-restriction part
needed beyond the mask lanes; it alone is not a proof of full-payload (ii).
The remaining components must admit a compatible lift. Similarly,
surjectivity of the unrestricted round projection alone would not establish
(i). No unrestricted ambient-surjectivity or rank theorem has been claimed.

| Tape block | Raw independent F coordinates |
|---|---:|
| Ten mask-only columns | 10 × 1024 = 10,240 |
| G and D | 2 × 1024 × 4 = 8,192 |
| **M** | **18,432** |
| H1-padding samples | 1024 × 4 = 4,096 |
| Eligible noise | 3,803 |
| **N** | **7,899** |
| **T = M ⊕ N** | **26,331** |

These are dimensions of the raw tape spaces, not ranks after balancing or
observation, and not a claimed dimension of `silentMasks`. The unchanged
eligible counts by semantic column are
`222,222,223,224,224,224,224,224,224,248,249,259,259,259,259,259`.
There are 214 copy-active and 810 copy-inactive rows. The natural-number
inventory is retained in `/tmp/aspis-d12/evidence/d12-layout-inventory.json`.

Writing q for the arbitrary challenge query set's cardinality:

| Disclosed projection | Ambient K slots | At q = 22 |
|---|---:|---:|
| Round-polynomial arrays | 280 | 280 |
| Semantic C1 claims and openings (`c1Map`) | 16 × (5 + 4q) | 1,488 |
| Other 13 columns' claims and openings | 13 × (5 + 4q) | 1,209 |
| Mask-sum, inactive sum, opening/final coefficients | 265 | 265 |
| Complete payload | 690 + 116q | 3,242 |
| Non-round payload | 410 + 116q | 2,962 |

The fixed zero-extended payload type still has 30,409,394 K coordinates.
Unqueried slots disclose zero. q22 is only a labelled count, not a restriction
of the universally quantified Challenges type. Compare these ambient K-slot
counts to F-coordinate dimensions only after multiplying by `[K:F]`;
`PackBasis F` alone does not assert that K has dimension four. Encoder,
sumcheck, subfield and balance constraints have not been subtracted as ranks.

### Host checks and exact evidence

Host/workspace: `dombarker@100.108.41.90`,
`/home/dombarker/project-offloads/aspis-fs-generic-20261006`.
Lean 4.32.0 (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`) and Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997` were rechecked. The existing
shared-lock launcher was read before use. Each source installation and
focused `lake env lean` invocation held `/tmp/aspis-r0-lean.lock`.
One process per attempt, `-j1 -M7000 -DElab.async=false`, 900-second timeout,
MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128. Every admission
was 24+7 GiB under the 55 GiB reservation ceiling. No limit was raised.

No package-wide replay, cold dependency build, SBF/Rust gate, finite-field
elimination or rank computation ran. The early premature dependent attempt
3155 returned immediately because the partition object did not yet exist;
subsequent dependent checks used green predecessors. Affected sources were
recompiled after the checker-instance correction and final whitespace fix;
no unchanged full regression was repeated.

Kernel-memory failures 3157/3158 were isolated to evaluation of the H1
padding's concrete finite-set sum. The replacement proves balancing of a
zero family with the finite set abstract, then applies the named theorem.
Failure 3164 was the aggregate `run_split`; eight separately proved payload
components replace the aggregate reduction. Recursion failures in the final
HVZK wrapper were traced to a private-but-global decidability instance in
the helper checker: it changed the inferred finite tape construction. The
replacement makes both checker instances **local**, preserving the existing
`JointView` finite law. No statement, field premise, or resource limit was
weakened to fix these failures.

Source revision for every receipt is the requested base **01920c658** plus
its exact target snapshot SHA below and the latest preceding accepted
snapshots of its new imports. The twelve inherited critical source files
were matched byte-for-byte with the host, recorded in
`/tmp/aspis-d12/evidence/dependency-hashes.json`; unchanged compiled caches
were reused. Source snapshots, SHA receipts, outputs, GNU-time logs, the
attempt inventory and natural layout inventory are retained on the host
and in `/tmp/aspis-d12/evidence/`, outside the commit. Final local sources
match their accepted host snapshots byte-for-byte.

“Standard” means only `propext`, `Classical.choice`, `Quot.sound`, or a
subset. Failed attempts are rejected in full, irrespective of partial
`#print axioms` output. The final requested declarations
`R0Z.D12.M_pure`, `R0Z.D12.decomposition`, and
`R0Z.D12.hvzk_perfect_of_maskImage` each print **exactly those three standard
axioms** in attempt 3184. `g_zero` and `other_components_affine` do as well.

| Attempt | Exact target | Exit | Wall | Peak RSS (KiB) | Swap | Result / axioms |
|---|---|---:|---:|---:|---:|---|
| 3154 | `R0Z/Partition.lean` | 1 | 0:05.76 | 6,813,040 | 0 | Rejected: partition projection/if proof plumbing. |
| 3155 | `R0Z/PayloadSplit.lean` | 1 | 0:00.12 | 189,188 | 0 | Rejected before elaboration: predecessor object absent. |
| 3156 | `R0Z/Partition.lean` | 1 | 0:05.64 | 6,816,432 | 0 | Rejected: dependent-if/projection proof plumbing. |
| 3157 | `R0Z/Partition.lean` | 1 | 0:07.00 | 7,169,696 | 0 | Rejected: kernel memory limit in pureTrace_fixed. |
| 3158 | `R0Z/Partition.lean` | 1 | 0:07.08 | 7,170,664 | 0 | Rejected: isolated padding proof still normalized the concrete set. |
| 3159 | `R0Z/Partition.lean` | 0 | 0:05.81 | 6,847,276 | 0 | Standard; abstract-set balance lemma fixes kernel reduction. |
| 3160 | `R0Z/PayloadSplit.lean` | 1 | 0:04.31 | 6,822,344 | 0 | Rejected: round projection type and component equality plumbing. |
| 3161 | `R0Z/HelperInvariant.lean` | 0 | 0:02.99 | 6,821,672 | 0 | propext/Quot.sound; first four-record helper preflight. |
| 3162 | `R0Z/PayloadSplit.lean` | 1 | 0:07.68 | 7,158,920 | 0 | Rejected: excessive definitional unfolding in aggregate payload proof. |
| 3163 | `R0Z/HelperInvariant.lean` | 1 | 0:08.11 | 6,813,000 | 0 | Rejected: endpoint-tuple Prod.ext plumbing. |
| 3164 | `R0Z/PayloadSplit.lean` | 1 | 0:08.41 | 7,169,744 | 0 | Rejected: kernel memory limit in aggregate run_split. |
| 3165 | `R0Z/HelperInvariant.lean` | 0 | 0:08.29 | 6,825,424 | 0 | Standard; complete helper/endpoint invariance. |
| 3166 | `R0Z/PayloadSplit.lean` | 0 | 0:09.59 | 7,009,360 | 0 | Standard; eight component lemmas, run_split and M_pure. |
| 3167 | `R0Z/JointTrace.lean` | 1 | 0:04.54 | 6,813,408 | 0 | Rejected: missing explicit base field on zero noise. |
| 3168 | `R0Z/AbsorptionLaw.lean` | 1 | 0:03.03 | 6,691,188 | 0 | Rejected: explicit equivalence sum needed. |
| 3169 | `R0Z/JointTrace.lean` | 1 | 0:04.08 | 6,815,884 | 0 | Rejected: conditional/zero-projection normalization. |
| 3170 | `R0Z/AbsorptionLaw.lean` | 0 | 0:03.19 | 6,721,648 | 0 | Standard; fixed-N law and uniform mixture. |
| 3171 | `R0Z/JointTrace.lean` | 0 | 0:04.30 | 6,850,460 | 0 | Standard; joint trace affinity. |
| 3172 | `R0Z/D12.lean` | 1 | 0:04.76 | 6,807,328 | 0 | Rejected: explicit field/wrapper elaboration. |
| 3173 | `R0Z/D12.lean` | 1 | 0:05.05 | 6,812,812 | 0 | Rejected: finite-tape instance mismatch at metadata wrapper. |
| 3174 | `R0Z/D12.lean` | 1 | 0:04.95 | 6,812,520 | 0 | Rejected: finite-tape instance mismatch, limits unchanged. |
| 3175 | `R0Z/AbsorptionLaw.lean` | 0 | 0:03.31 | 6,721,664 | 0 | Standard; generic law transport added. |
| 3176 | `R0Z/D12.lean` | 1 | 0:04.90 | 6,814,592 | 0 | Rejected: unsaturated wrapper unfolding and finite-tape instance mismatch. |
| 3177 | `R0Z/D12.lean` | 1 | 0:04.93 | 6,812,372 | 0 | Rejected: finite-tape instance mismatch remains. |
| 3178 | `R0Z/D12.lean` | 1 | 0:04.88 | 6,811,444 | 0 | Rejected diagnostic: identical displayed goals exposed instance mismatch. |
| 3179 | `R0Z/HelperInvariant.lean` | 0 | 0:08.37 | 6,843,688 | 0 | Standard; checker instances made local. |
| 3180 | `R0Z/JointTrace.lean` | 0 | 0:04.40 | 6,848,784 | 0 | Standard; dependent trace check after instance-scope correction. |
| 3181 | `R0Z/D12.lean` | 0 | 0:05.26 | 6,847,864 | 0 | Standard; D12 decomposition and perfect HVZK. |
| 3182 | `R0Z/PayloadSplit.lean` | 0 | 0:08.66 | 7,037,904 | 0 | Standard; final PayloadSplit after whitespace-only cleanup. |
| 3183 | `R0Z/JointTrace.lean` | 0 | 0:04.26 | 6,849,252 | 0 | Standard; dependent trace check against final payload source. |
| 3184 | `R0Z/D12.lean` | 0 | 0:05.13 | 6,847,672 | 0 | Standard; final D12 and requested axioms audit. |
| 3185 | `R0Z/Z4Maps.lean` | 0 | 0:03.93 | 6,849,016 | 0 | Standard; Z4 maps and unproved target statements. |

| Attempt | Exact target source SHA-256 |
|---|---|
| 3154 | `b82f6491b265cd8f9eb5e17e9f78dfe37cf0ad7661d5fdfa43b1b17f51821d94` |
| 3155 | `00d3c9fba7321825d8557336f3b1995c71424002cb54e2a1398ff43e7452f953` |
| 3156 | `66de3a7b386df646693ccc49a21f5a90d1ac26bce491f68643fc8819b0fbf85a` |
| 3157 | `71d554f68b56eecbe9fbfd647ad6f6c7c90b79ca48c9a718e37c34e450741a70` |
| 3158 | `09d83c7f0e8afb24b1b166a8c7fe38c75e67ce4d39be12376eaa22aa6daa2d59` |
| 3159 | `138e2bdce877cfc8d962e11cb1e0110eeb23c0c9623182d927c38dc07ad95c0f` |
| 3160 | `00d3c9fba7321825d8557336f3b1995c71424002cb54e2a1398ff43e7452f953` |
| 3161 | `617a5cc949e6cace14e913c0f610ff35672eabbea3277cce6f1c367b3b1792c1` |
| 3162 | `eeff8507bbfa57db568d340b53ff05533000157711be31d8fb184e6170793a08` |
| 3163 | `36e58f219d20b4bfbe929a5ef9998110a7d942a94a225f952c05742323d67ec7` |
| 3164 | `b9042750ec24388dfec276fd0f61fc56098f577d6b06266907a5d29923b19902` |
| 3165 | `3f276710896725b4637f226e9c0aed3804563ea41f013ad26cd85f97c0e4d60e` |
| 3166 | `2c42c149a4a3f6c678d114aa1417fe115838ace9516c09bb4232e20077e22b3d` |
| 3167 | `d34fcbd58dd834df952648bacb32e703bf72369902576bda797ff1d75b658b0c` |
| 3168 | `f0c6469fc08e128850c22414703971d90ebbab5ef9ce6c6f63d84842e318abfe` |
| 3169 | `c6cc0cb0b31f6af8abb35d0d083598bfcecbfa9d169a4fbfc9d4f868ec545194` |
| 3170 | `8049fe8fb2d0a461f629707967178f2232b5fe0689e1cef5476f9f42581c3b43` |
| 3171 | `4ce83bf414496872279fe3558e467fb4c57eaa3e143b8acc15ec43169c1fe8f4` |
| 3172 | `895658c44ffa3460d27c0b9cd8ea9075919bb9d93e4dc82c89943ec8543f3ab6` |
| 3173 | `f1060e6368f566f310f71f8dcffd40964d565df31606a7ac83950951070b342a` |
| 3174 | `727566fcde985543481b1f0b788f305f6138c5fdc0648451574b7dfc9595b3d9` |
| 3175 | `17765d9354db921f467e0d01087ad9f1ef8b4e10977a8d7e5028f50d17072c52` |
| 3176 | `452fd91ed9d71dc78dc290cc21958dcb96d2d3e81b87a619ae46f23751ab9d2a` |
| 3177 | `bbfe5543d3ff118112c405892583afcfee40c79ca5e5333101198830dd546585` |
| 3178 | `33efe65189a78ce8f9c67e93daa250f986ee3670efd95e3b7f005a58364c6831` |
| 3179 | `60f50f7df9c4981ec38d5eb32da57f19f7af6a007b1e771368a4a31abf01d6e3` |
| 3180 | `4ce83bf414496872279fe3558e467fb4c57eaa3e143b8acc15ec43169c1fe8f4` |
| 3181 | `ea3dce2090059f9b657b85cdd0fc518d238535e13752b70049f83b29a6b6f4bf` |
| 3182 | `0ee03c1176b261b6aba55e09e08f99476ecbe375dd13bb08412caf39cff605a3` |
| 3183 | `4ce83bf414496872279fe3558e467fb4c57eaa3e143b8acc15ec43169c1fe8f4` |
| 3184 | `ea3dce2090059f9b657b85cdd0fc518d238535e13752b70049f83b29a6b6f4bf` |
| 3185 | `5bfcf18abda146c643aabaf1795fa920ac71e2628126e4ec1a40c59c8ea8bc52` |

Final accepted target attempts: Partition 3159, PayloadSplit 3182, HelperInvariant 3179, JointTrace 3183, AbsorptionLaw 3175, D12 3184, Z4Maps 3185.

The scoped forbidden-token and whitespace/diff checks pass. There is no
new sorry, axiom, unsafe declaration, native evaluation, or elaboration-limit
override. Literal reduction is confined to the small natural endpoint
checks and the three-slot tape permutation; no trace, field, encoder,
recurrence or rank matrix is normalized. Commit scope is these seven new
privacy modules and this LOG. No soundness/Rust/FS file, wallet, account,
key or authority was changed. No co-author trailer. Z3b's D12 conditional
result is complete; Z4 stops at maps, target statements and dimension counts.

### Lead decisions after Z4a — D13 (transport reinstated), Z4b (remainder containment)

Z4a (`z4/z4a/FINDINGS.md`) is accepted as computation. Two findings, two decisions.

**D13 — the message-index transport returns.** The C1 opening map's rank
collapse on structured fibre sets (`{0,…,21}`: residues 1,2 at rank 6) is
caused by the padding rows sitting in one natural-basis residue class
(`N_{4k+3}(T) = T·D₁(T)·N_k(D₂(T))`). The historical R16 transport
(`v8-full-view-zk-20260912/tools/r16_basis_transport.rs`: pivot 1023, the
first 89 inactive rows legal in all sixteen semantic columns at coefficient
indices 0–88, remaining rows in order, pivot last) places the free rows at
the lowest natural indices of every residue class, so the eligible-cell
restriction spans the same polynomial-degree prefix as the full message at
every fibre set. The lead withdrew the transport on 2026-10-09 ("no R16
transport") in error. Decision: reinstate it as a fixed permutation
`π : rows → coefficient index` with that generating rule, in both the Rust
(`Enc(t ∘ π⁻¹)`, weights/indicator/eqWeight composed with π) and the Lean
glue (`SemD3Glue`, `MaskView`, `R0Z.HonestView`: words are `Enc (π t)`,
`Data.points/inactive` are stated in coefficient space). The agreement,
chord and fold theorems concern the code and messages and are unchanged.
Twin fibres (equal `T_u`) are not a hiding failure: the honest symbols
satisfy the same dependency, so the displacement space shrinks with the
image. The C1 part of (ii) is then provable structurally: eligible
restriction and full restriction have the same image at every `S`.

**Z4b — the remainder must be tested against the 988-dimensional pure
image with real traces.** Z4a's `M` excludes the sixteen semantic columns'
eligible cells, which the Rust gate counted as mask sources (even-exponent
factors). Under D12 those cells are in `N` because the original multiplies
them. Whether `(g w n, 0) ∈ range (A ∘ inl_M)` for actual honest traces and
generic challenges is therefore an open computation, as is the round-polynomial
part of (ii). If containment fails, the mask design changes (more mask-only
columns with the missing leading degrees, D14); if it holds, Z4's route is the
structured family of Z4a plus a containment lemma. The θ = 0 obstruction is a
degenerate-challenge event: D8's ε = 0 becomes ε ≤ mass of an explicit
bad-challenge set (θ = 0 at least), to be fixed once Z4b reports.

### Lead acceptance of Z4b (`z4/FINDINGS-B.md`); decision D14

Accepted as computation (host `nuc`, capped 3/4 GiB, swap 0: build 4.0 s,
probe 400 s, peak child RSS 102 MiB, cgroup peak 151 MB, 187 source hashes
checked, exit 0). Ten genuine same-statement pair-forest instances, twenty
challenge vectors, one hundred tests per condition: D12's (i) fails for both
remainder definitions, (ii) fails, and the 26-column repair leaves exactly a
four-dimensional excess at the last round's value in every case.

**Reading.** The excess is the linear functional
Φ(rounds, claims) = p₉(α₉) − Σ_c f_c(α)·y_c. It vanishes on every linear
mask displacement with zero claims (a silent mask has p₉(α₉) = 0), and on the
honest view it equals η·O(y(α)), the original terminal evaluated on the
*disclosed* current-point claims. That is the verifier's terminal-consistency
check: a deterministic function of other disclosed coordinates, which carries
no information beyond them and which a simulator computes. D12 asked for it to
lie in a linear image, which no linear mask can provide, so Z4b's "no column
count repairs this" is a statement about D12's wording, not a hiding failure.
Two consequences.

**(a) D12 restated (supersedes its clauses (i), (ii)).** Fix the round-9
direction d(X) = X − ½; d(0) + d(1) = 0, so adding a multiple of d preserves
the sumcheck boundary chain, and d(α₉) ≠ 0 iff α₉ ≠ ½. Let
Φ₀(v) := p₉ᵛ(α₉) − maskLinear(yᵛ), linear in the payload v and zero on silent
masks. Define the payload bijection Ψ_ch(v) := v + η·O(yᵛ)·d/d(α₉) on the
round-9 coefficients; it depends only on ch and on v's claim coordinates, and
its inverse subtracts the same term. From D12's exact decomposition,
view(w,m,n) = Ψ_ch(c̃(w) + A(m,n) + (s(w,n), 0)) with
c̃(w) := c(w) − η·O(y_w(0))·d/d(α₉) and
s(w,n) := g(w,n) − Φ₀(g(w,n))·d/d(α₉). New MaskImage:
(i′) ∀ w n, (s(w,n), 0) ∈ range(A ∘ inl_M);
(ii′) ∀ w w′, c̃(w) − c̃(w′) ∈ range A.
HVZK_perfect follows by the D12 proof (absorption, mixture, coset) followed by
pushforward under the fixed bijection Ψ_ch; α₉ = ½ joins D8's bad-challenge
set (ε ≤ |bad|/|K|). Z4b's data support (i′) and (ii′) exactly where the only
excess was Φ: for the 26-column mask in all one hundred tests; for the current
ten-column mask, not.

**(b) The real deficiency is 88 dimensions in rounds 8–9**, not Φ: the silent
pure image has rank 988 of the 1076 that (i′) needs. Each mask column adds one
K-dimension to the last round (its slice is λ(X − α₉)), so a column-only repair
needs 26 M31 columns plus G: width 45, every `Fin 29`/`width29` in R0, R0P and
R0Z, sixteen more committed lanes, about +55 % prover work and opening size.
Decision: add a **Libra tail** to the mask instead. Two univariates
h₈, h₉ ∈ K[X] of degree ≤ 27, coefficients stored in lane 28 (D, K-valued) at
coefficient indices 0–27 and 28–55 (rows π⁻¹(0..55) under D13; D is mask-only,
so every row is free). The masked terminal gains + h₈(a₈) + h₉(a₉); the
hypercube total 2⁹·Σ_j (h_j(0) + h_j(1)) enters the mask total already
disclosed in the mask-sum round; the verifier reads h₈(α₈) + h₉(α₉) through a
**fourth opening weight row** w_h, w_h(j) = α₈^j for j ≤ 27, α₉^(j−28) for
28 ≤ j ≤ 55, 0 otherwise, applied to all 29 lanes like the three point rows
(29 more disclosed claims; the terminal reads lane 28's only). Soundness: the
terminal stays of degree 27 in every variable (the existing VDeg-27 bound), and
the new claim is bound to the commitment by the same quotient argument as the
point claims (B4's polynomial becomes degree 4, card ≤ 400). Privacy: rounds 8
and 9 each gain up to 27 silent dimensions, less the shared Φ₀ and mask-total
constraints; the target is silent rank 1076 and (i′), (ii′) on Z4b's tests.
Width, lane roles 16–27, the eligible-noise design and D13 are unchanged.
**This choice is provisional on Z4c.** If Z4c fails, the fallback is the
26-column design, for which Z4b already shows 1076 and (i′), (ii′) on all
samples.

**Z4c (privacy Codex; computation; no Lean; no production Rust).** Base: the
current `origin/v8-reference` head, which includes R-G's transport. Extend
`z4/probe.rs`: (1) opened-symbol and OOD observations through
`aspis_core::r0::transport` (coefficient space, D13); (2) the Libra tail in
lane 28 as above, with the fourth weight row's 29 claims as observations and
the mask total including the h terms; (3) Φ₀ and Ψ_ch as in (a). Report, for
Z4b's twenty challenge vectors × five pairs: the silent mask image rank (target
1076); (i′) and (ii′) pass counts; the (i′) excess support if any; C1 rank per
semantic column with the extra row, on the random fibre set and on {0,…,21}
(the transport should make both full: 112 per column); the 26-column control
(expected 1076, (i′) and (ii′) 100/100); Z4b's degenerate controls under (i′)
and (ii′); the α₉ = ½ event. Same caps (≤ 4 GiB, swap 0), same evidence
format (`FINDINGS-C.md`, `evidence-C.json`, `summary-C.json`, `probe-C.log`),
commit on `codex/z4c-libra-20261009`. Stop list: any pass count below 100/100
for the Libra design (report the excess coordinates and stop); any C1 rank
below 112 per column on the random set; any helper-pole abort; any change to
Lean or production Rust.

### Lead decision D13′ — exact form of the transport in the Lean model (job T1)

D13 located the Lean change in the glue. Inspection shows it must enter the
opening layer, because the verifier's point-claim and inactive weights are
themselves transported and `R0FS.Witness` states them. The design below fixes
the statements; the proofs are reindexing and linearity.

1. `R0/OpeningDefinitions.lean`: `Data` gains `transport : Fin 1024 ≃ Fin 1024`
   (π). New `coeffWeight (π) (w : InitialMessage K) : InitialMessage K :=
   fun j => w (π.symm j)`, a row-stated weight in coefficient space.
   `discrepancy D t j l := D.pointClaims j l −
   dot (coeffWeight D.transport (eqWeight (D.points j))) (t l)`;
   `inactiveDefect D γ v t := v −
   dot (coeffWeight D.transport (indicator D.inactive)) (curve t γ)`;
   `weights D κ := coeffWeight D.transport
   ((∑ j, κ^(j+1) • eqWeight (D.points j)) + indicator D.inactive)`.
   `eqWeight`, `indicator`, `claim`, `claimPrime`, `qWeights`, `totalWeights`,
   B1–B7, V1, V2 and `Accept` are unchanged in text. Lemmas:
   `coeffWeight_add`, `coeffWeight_smul`, `coeffWeight_sum`,
   `dot_coeffWeight_left : dot (coeffWeight π w) m = dot w (fun r => m (π r))`
   (`Equiv.sum_comp`), `dot_coeffWeight_indicator :
   dot (coeffWeight π (indicator I)) m = ∑ r ∈ I, m (π r)`.
   If Z4c adopts the Libra tail, the same job adds
   `extraWeight : InitialMessage K` (already coefficient-indexed) and
   `extraClaims : Fin 29 → K`, the term `κ^4 • extraWeight` in `weights`,
   `κ^4 · width29Batch extraClaims γ` in `claim`, a fourth discrepancy row,
   `pointPolynomial` of degree 4 and `B4_card ≤ 400`.
2. `R0/OpeningAlgebra.lean`, `R0/Binding.lean`, `R0/BadSetBounds.lean`: adapt.
   `binding`'s conclusion becomes
   `D.pointClaims j l = dot (coeffWeight D.transport (eqWeight (D.points j))) (t l)`
   and `v = ∑ r ∈ D.inactive, exactInitialMessageCurve t γ (D.transport r)`.
   `wideBinding` is unchanged (`type_of%`).
3. `R0FS/Protocol.lean`: `Stmt` gains `transport`; `data` passes it; `Witness`
   clause 2 uses `coeffWeight x.transport`. `Hypotheses.accept_not_doomed` keeps
   its statement.
4. R0P: `SemView.TypedContext` gains `transport`; `openingStmt` sets
   `transport := x.transport`. New in `SemView`:
   `coeffsOf (π) (t : Trace K) : Fin 29 → InitialMessage K := fun c j => t c (π.symm j)`,
   `rowsOf (π) m : Trace K := fun c r => m c (π r)`, their inverse lemmas,
   `coeffsOf_padC2Trace`, `dot_coeffWeight_coeffsOf :
   dot (coeffWeight π w) (coeffsOf π t c) = dot w (t c)`, and
   `LambdaRows (π) (W) : Finset (Trace K) := (Lambda W).map (rowsEquiv π)` with
   `mem_LambdaRows : t ∈ LambdaRows π W ↔ coeffsOf π t ∈ Lambda W` and
   `card_LambdaRows`. Every semantic candidate quantification
   `t ∈ Lambda (c2Words x h g)` (SemD2 `candidates`, SemD3Glue, SemPad,
   MaskNoHit, MaskPrefix, MaskEarly, MaskD3Glue) becomes
   `t ∈ LambdaRows x.transport (c2Words x h g)`. In the two glue theorems the
   opening witness `m` yields `t := rowsOf x.transport m`; `hy` uses
   `dot_coeffWeight_coeffsOf`; `witness_baseTyped` descends through `coeffsOf`.
   Row-space uses of `eqWeight` (`SemHonest`, `SemDeg`, `honestClaims`) are
   untouched. `combined_fiat_shamir_masked` changes only through the new field
   of `TypedContext`.
5. R0Z: `HonestView.openingWeights`, `batchLinear`, `linearPayload`,
   `payloadAffine`, `run` take an explicit `(π : Fin 1024 ≃ Fin 1024)`. With
   `coeffsLinear π : InitialMessage K →ₗ[K] InitialMessage K`
   (`LinearMap.funLeft K K π.symm`): `.ood j c ↦ oodLinear (ch.circle j) ∘
   coeffsLinear π ∘ proj c`; `.opened q s c ↦ proj (childIndex q s) ∘
   exactInitialLinear ∘ coeffsLinear π ∘ proj c`; quotients on
   `coeffsLinear π ∘ proj c`; `.pointClaim` and `.inactiveSum` unchanged (row
   space; equal by `dot_coeffWeight_coeffsOf`);
   `openingWeights π ch := totalWeights ⟨0, z₀, z₁, 0, openingPoints (alpha ch),
   0, copyInactiveRows, π⟩ …`. `ZkStatement.HonestProver` gains `transport`;
   `payload`, `view` and `proverOutput` pass `h.transport`; the words are
   `exactInitialEncoder (coeffsOf h.transport t c)`.
   `D12.hvzk_perfect_of_maskImage` keeps its statement with π threaded. State
   `D13Order (π) : Prop` in R0Z (for k < 89: `π.symm k ∈ copyInactiveRows` and
   `∀ c < 16, eligible c (π.symm k)`; `π 1023 = 1023`; the remaining rows in
   increasing order) for Z4's later use; no concrete instance is proved (that is
   a Rust refinement fact, witnessed by R-G's statement test).
6. Replay: stage `R0/*.lean` into `sources/R0/` on the host; compile the import
   closure of the changed modules in dependency order with
   `sh run2.sh N Module 7000 7` from attempt 3282; final targets `R0P/MaskAll`
   and `R0Z/Z4Maps` (the closure of `R0Z/D12`); `#print axioms` for
   `wideBinding`, `combined_fiat_shamir_masked`, `hvzk_perfect_of_maskImage`.
   Stop list: any statement change beyond those listed; any proof needing more
   than linearity and reindexing facts about `coeffWeight`; any module above
   the cap or 900 s; `sorry`, `axiom`, `native_decide`, `maxHeartbeats`, and
   concrete `Finset.univ` over rows are forbidden.

**T1 is held until Z4c reports**, so that `Data` is changed once, with or
without the fourth weight row. Two full chain replays would otherwise follow.

### Lead acceptance of Z4c (`z4/FINDINGS-C.md`); decisions D15 and D14′; job T1 issued

**Verdict.** Z4c is accepted and D14 is confirmed. The Libra tail (h₈, h₉ in
lane 28, coefficient cells 0–55, read through the fourth weight row w_h) gives
silent mask rank 1076 on all 20 challenge vectors. 1076 is the upper bound
(1080 from the initial-zero boundary chain, less one K equation for the
terminal), so the computed rank is exact, not a lower bound. (i′) and (ii′)
pass 100/100; the derivative diagnostic 100/100; every semantic column has C1
rank 112 on both the random fibre set and {0,…,21}, so D13's transport makes
the consecutive set full rank as intended; the 26-column control matches
(1076, 100/100). Receipts in `z4/evidence-C.json`: probe exit 0, 2423.5 s,
peak child RSS 39.3 MiB, cgroup peak 51.4 MiB, swap 0, MemoryHigh 3G /
MemoryMax 4G; 189 compiled-source and 15 decision-source hashes verified; an
exact replay of Z4b's 100 targets. The 26-column fallback (width 45) is
retired; the width stays 29. Evidence is on `v8-reference` as 52a538c48.

**Degenerate controls.** 24 of the 26 controls (θ=0, μ=0, η=0, θ=μ=0, each
α_j ∈ {0,1} alone) pass with exact rank 1076. The two fully Boolean vectors
α = 0¹⁰ and α = 1¹⁰ give constructed ranks 1022 and 1038, one excess (i′)
dimension each (and one for (ii′) at α = 1¹⁰), supported in round 7 degrees
12–27 and round 8 degrees 2 and 27. The report is right to call these
unresolved rather than counterexamples: the probe's subspace is the
zero-batched-word lift and is only known to equal the full silent image when
it attains the bound. The mechanism is nevertheless clear. With a Boolean α
the eq-weights select rows instead of mixing them and the X(1−X) freedom of
every round vanishes at once; a single Boolean coordinate leaves the other
rounds' freedom intact, and those controls pass. α₉ = ½ is the pole of Ψ_ch's
direction d(X) = X − ½ (D14) and is confirmed undefined there.

**Decision D15 — generic-position hypothesis for MaskImage.** The Z4 Lean
route states MaskImage only on
`Good ch := (∀ j, alpha ch j ≠ 0 ∧ alpha ch j ≠ 1) ∧ alpha ch 9 ≠ 1/2`
(`MaskImageOn Good h B x`), and `hvzk_perfect_of_maskImage` becomes
statistical: the two laws are equal on `Good` (the D12 proof is pointwise in
`ch`, so this is a restriction of the quantifier, not a new argument) and the
distance is bounded by Pr[¬Good] ≤ 21/|K_α|, K_α the field the α rows are
sampled from: 2^−119.6 for QM31, 2^−243.6 for WideExact. The exclusion is
deliberately larger than the two observed failures so that the preimage
construction may divide by α_j(1−α_j) in any round. If the containment proof
needs a further nonvanishing condition it is added by a numbered decision with
the probability recomputed; nothing else about D14 changes. The probe's other
qualifications (helper pole χ = compressed_tuple(λ), γ = 0, singular or
coincident OOD points) are honest-prover abort or FS sampling events already
in the FS layer's bad sets and are not part of `Good`.

**Refinement note ZR3.** `SPEC.md` line 7 instantiates Lean's `K` with E,
while the Rust reads the semantic α rows as QM31 embeddings (`onchain.rs`
`eq_at`, "K embeddings from the checked semantic alphas"). The Lean FS theorem
thus quantifies over a larger challenge space than the Rust samples. This is a
Lean↔Rust correspondence obligation for the refinement block (with G14/G18),
recorded here and not acted on in T1.

**Decision D14′ — exact Lean form of the Libra tail.** D13′ item 1 placed the
fourth row in the opening layer. `R0P/MaskProtocol.lean` shows the mask enters
the semantic terminal through the abstract
`maskClaims : (Fin 29 → K) → (Fin 10 → K) → K` applied to the first point's
claims `y 0` and `alpha`, with `MaskDegree` (VDeg 27 per variable) and
`maskTotal` by `bsumB`. h₈(α₈) + h₉(α₉) is not a function of `y 0` (which is
multilinear in α), so the tail needs the extra claims as an argument:

1. `R0P/MaskProtocol.lean`:
   `maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K`
   (first point claims, extra claims, alpha).
   `terminalZ maskClaims pub lam chi theta mu eta zc B y yx alpha :=
   maskClaims (y 0) yx alpha + eta * terminalValue pub lam chi theta mu zc B y alpha`.
   `libraWeight (alpha : Fin 10 → K) : InitialMessage K := fun j =>
   if j.val < 28 then alpha 8 ^ j.val else if j.val < 56 then alpha 9 ^ (j.val − 28) else 0`
   (coefficient-indexed; no transport).
   `honestExtra (π) (t : Trace K) (alpha) (l) : K := dot (libraWeight alpha) (coeffsOf π t l)`.
   `virtualPolyZ`, `maskTotal` and `MaskDegree` pass `honestExtra π t alpha`
   as the second argument; `virtualPolyZ_total` and `virtualPolyZ_vdeg` keep
   their form.
2. `R0P/MaskValue.lean` (concrete instance):
   `maskClaimsR0 y0 yx alpha := (current value) y0 alpha + yx 28`.
   `MaskDegree`: the current proof plus
   `VDeg 10 (fun _ => 27) (fun alpha => ∑ j : Fin 28, c j * alpha 8 ^ j.val + ∑ j : Fin 28, c' j * alpha 9 ^ j.val)`
   (degree ≤ 27 in variables 8 and 9, constant in the others). The hypercube
   total 2⁹·(h₈(0)+h₈(1)+h₉(0)+h₉(1)) is `maskTotal` by definition; no
   separate statement.
3. Opening layer (D13′ item 1, second paragraph, made exact):
   `Data.extraWeight : InitialMessage K`, `Data.extraClaims : Fin 29 → K`;
   `weights D κ := coeffWeight D.transport ((∑ j, κ^(j+1) • eqWeight (D.points j)) + indicator D.inactive) + κ^4 • D.extraWeight`;
   `claim` gains `+ κ^4 * width29Batch D.extraClaims γ`;
   `extraDiscrepancy D t l := D.extraClaims l − dot D.extraWeight (t l)`,
   `extraDefect D γ t := width29Batch (extraDiscrepancy D t) γ`;
   `pointPolynomial := C (inactiveDefect …) + ∑ j : Fin 3, monomial (j+1) (pointDefect …) + monomial 4 (extraDefect …)`;
   `B4` filters on `pointDefect D γ t ≠ 0 ∨ extraDefect D γ t ≠ 0`;
   `B4_card ≤ 400`; `binding` concludes in addition
   `∀ l, D.extraClaims l = dot D.extraWeight (t l)`. `wideBinding` by `type_of%`.
4. `R0FS/Protocol.lean`: `Stmt.extraWeight`, `Stmt.extraClaims`; `data`
   passes them; `Witness` gains `∀ l, x.extraClaims l = dot x.extraWeight (t l)`.
   The extra claims are disclosed with the point claims (before the circle
   rows) and absorbed as they are.
5. R0P glue: `TypedContext.extraClaims : Fin 29 → K`; `openingStmt` sets
   `extraWeight := libraWeight (alpha ch)` and `extraClaims := x.extraClaims`;
   the semantic verifier's terminal is `terminalZ … y x.extraClaims alpha`;
   the two glue theorems carry `honestExtra` through `witness_baseTyped`
   (coefficient space via `coeffsOf`; no `coeffWeight`).
6. R0Z: payload coordinate `.extraClaim (c : Fin 29)` with
   `linearPayload … (.extraClaim c) := dotLinear (libraWeight (alpha ch)) ∘ coeffsLinear π ∘ proj c`;
   `HonestProver.payload`, `view`, `proverOutput` disclose it; `nonRound`
   keeps it (not a round coordinate); `D13Order` unchanged. `D12.MaskImage`
   and `hvzk_perfect_of_maskImage` keep their form; D15's `Good` belongs to
   the Z4 route (T2), not to T1.
7. Soundness constant: B4's card 300 → 400 changes the opening-layer union
   bound by 100/|E|. `combined_fiat_shamir_masked` records the new constant
   exactly; it is reported, not rounded away.

**Job T1 (Lean Codex) = D13′ + D14′: one job, one replay.** Base: the
`origin/v8-reference` head carrying this section. Branch
`codex/t1-transport-libra-20261009`. Order of work: `R0/OpeningDefinitions`
→ `R0/OpeningAlgebra`, `R0/Binding`, `R0/BadSetBounds` → `R0FS/Protocol` →
`R0P/SemView` (D13′ item 4: `transport`, `coeffsOf`, `rowsOf`, `LambdaRows`,
`dot_coeffWeight_coeffsOf`, `openingStmt`) → `R0P/MaskProtocol` →
`R0P/MaskValue` → the Mask*/SemD* glue (`LambdaRows` quantification;
`honestExtra` via `coeffsOf`) → `R0P/MaskInstance` (new constant) → R0Z
(D13′ item 5 and D14′ item 6). Proof route: reindexing (`Equiv.sum_comp`),
linearity of `coeffWeight`/`coeffsOf`, and the degree lemma for the two
univariates; nothing else. Replay per D13′ item 6 from attempt 3282, one
module at a time under `flock /tmp/aspis-r0-lean.lock`; final targets
`R0P/MaskAll` and `R0Z/Z4Maps`; `#print axioms` for `wideBinding`,
`combined_fiat_shamir_masked`, `hvzk_perfect_of_maskImage`. Stop list: D13′
item 6's list; any statement change beyond D13′/D14′; any change to the
soundness bound other than the B4 term; any edit to `R0C/SemStatement.lean`
or `R0C/CircleRows.lean` (lead-only).

**After T1: T2 (Z4 Lean route)** — `Good`, `MaskImageOn`, statistical HVZK
with the 21/|K_α| term, then the structured mask family, Ψ_ch and
containment. Specified when T1 lands. **Rust R-H** (D14 in R-D/R-F/transcript:
lane-28 h cells, fourth weight row, 29 extra claims, terminal h-terms) follows
T1 so that the Rust is built to the replayed statement.

### T1 stop — fourth-row gamma collision is absent from B3 (2026-10-09)

**Status: stopped at statement inspection, before source edits or replay.**
Branch `codex/t1-transport-libra-20261009`, base
`41603fce0ca204804748a3ccad03c65f6eb536c1`. Read D13′ items 1–6 and
D14′ items 1–7 / Job T1 at that revision. Evidence:
[`t1/evidence.json`](t1/evidence.json). No Lean compilation attempts were
launched; attempt 3282 was not consumed by this job. No final-target or
axioms-audit result is claimed.

**Obstruction.** D14′ item 3 requires per-lane extra-claim equality, but its
new B4 predicate only yields `extraDefect D gamma t = 0`, i.e.
`width29Batch (extraDiscrepancy D t) gamma = 0`. Passing from this batched
equality to `extraDiscrepancy D t = 0` requires excluding the extra row's
gamma collisions. D13′ item 1 leaves B3 unchanged, and D14′ item 3 only
amends B4. The unchanged B3 ranges over the three point discrepancies and
does not inspect `extraClaims`.

The existing proof makes the missing step explicit:
`R0/Binding.lean:164` obtains batched defects from `B4_outside`, then
`:170` uses `B3_outside` to obtain per-lane point equality.
`R0/BadSetBounds.lean:66` restricts that latter lemma to `j : Fin 3`;
`R0/OpeningDefinitions.lean:76` likewise restricts B3 to those three rows.
All citations here refer to
`docs/research/v8-wide-reference-20261005/lean/` at the base revision.

For a fixed extra-discrepancy vector, take `e 0 = 1`, `e 28 = -1`, and
all other entries zero. The definition in
`AspisFormal/AspisFormal/V6Width29CorrelatedAgreement.lean:25` gives
`width29Batch e gamma = 1 - gamma^28`, so at the permitted nonzero
challenge `gamma = 1` the batch vanishes although `e ≠ 0` and the terminal's
lane 28 is wrong. This vector is fixed before gamma. Multiplication by
`kappa^4` cannot expose a zero batch. This is an algebraic obstruction to
the specified per-lane proof step, not a Lean-checked counterexample to the
entire binding theorem.

**Lead amendment required.** The direct extension of the existing argument
would add the extra row's nonzero collision set to B3. With the current
`batch_union_bound` and `Lambda_card` bounds, four rows give
`100 * 4 * 28 = 11200` instead of B3's 8400. The grouped gamma numerator's
14000 would become 16800, an additional `2800 / (|E| - 1)` term, alongside
the authorized B4 change `300 → 400` contributing `100 / |E|`.
These are the bounds of that proposed extension, not an implemented repair
or a claim of optimality. Changing B3 and its ledger exceeds the issued
statement and the instruction allowing only the B4 bound change, so no such
change was made. A new lead decision is needed before implementation resumes.

Read-only host preflight inspected `run2.sh` in
`/home/dombarker/project-offloads/aspis-fs-generic-20261006` on
`dombarker@100.108.41.90`: it invokes the shared
`flock /tmp/aspis-r0-lean.lock`, checks the 55 GiB aggregate reservation,
and for arguments `7000 7` specifies MemoryHigh=5G, MemoryMax=7G,
MemorySwapMax=0 and timeout 900 s. No sources were staged and no build scope
was started. All Lean and Rust sources, including both lead-only R0C files,
remain unchanged. This commit contains only this stop report and its JSON
evidence; no binaries or co-author trailer.

### Lead amendment D14″ — the extra row enters B3 (T1 re-issued)

T1 stopped correctly before any edit or replay (`t1/evidence.json`,
b11f5a644). D14′ item 3 bound the extra claims through B4 only. B4 forces
the γ-batch `width29Batch (extraDiscrepancy D t) γ = 0`, not the per-lane
equalities; the three point rows obtain per-lane equality from `γ ∉ B3`, and
I left the extra row out of B3. The worker's example is exact: discrepancies
e₀ = 1, e₂₈ = −1 have batch polynomial 1 − γ²⁸, which is zero at γ = 1.

**Decision.** B3 gains the extra row:
`B3 D := (Lambda D.W).biUnion fun t =>
  (Finset.univ.biUnion fun j : Fin 3 =>
    if discrepancy D t j = 0 then ∅ else width29NonzeroCollisionSet (discrepancy D t j)) ∪
  (if extraDiscrepancy D t = 0 then ∅ else width29NonzeroCollisionSet (extraDiscrepancy D t))`.
`B3_card ≤ 11200` (four rows × 100 candidates × 28 collision roots).
`B3_outside` gets the extra-row counterpart; `binding` concludes
`∀ l, extraDiscrepancy D t l = 0` from `h3bad` and the extra B4 clause, as
for the point rows. Soundness constant: the γ-group addend goes from 14,000
to 16,800 (+2,800/(|E|−1)) and the B4 card from 300 to 400 (+100/|E|). Both
are authorised; against ≈ Q·2⁻¹⁰⁵ the change is ≈ 2⁻²³⁶ per query.
`combined_fiat_shamir_masked` records the new constant exactly. T1's stop
item "any change to the soundness bound other than the B4 term" reads "other
than the B3 and B4 terms above". Everything else in D13′, D14′ and the T1
paragraph stands. T1 is re-issued on the head carrying this section.

### Lead note — reference-closure gate G_ref and the order of the remaining privacy work

User direction (2026-10-09): the reference is proved 100-bit sound and
privacy-preserving before any protocol optimisation; the optimisation target
is one transaction via `R0_SOUNDNESS.md` §8. The gate G_ref is defined in the
Rust PLAN ("Lead decision after user direction"). For this LOG it fixes the
order: T1 (D13′, D14′, D14″) → T2 (D15 `MaskImageOn Good`, `hvzk_stat`) →
ZF1 (ZK_FS composition with the ledger terms named) → the model-level abort
accounting (P3). ZR1–ZR3 are source refinement and are proved against the
deployed prover and verifier after §8.
### T1 completed — transport π, Libra tail, and fourth-row B3 (2026-10-09)

Implemented D13′, D14′ and D14″ on
`codex/t1-transport-libra-20261009`, based on
`fcb5701990e14ebab3c00c24729ddfea88517eb9`. The prior statement-level stop
remains recorded above and in `t1/evidence.json.previous_stop`; D14″ supplies
the missing extra-row gamma collision set.

The opening data and FS witness now carry π and the coefficient-indexed
extra row. `coeffWeight` transports the point and inactive weights;
`coeffsOf`/`rowsOf` and `LambdaRows` connect coefficient candidates to semantic
rows. Binding uses `B3_extra_outside` after the extra B4 clause to establish
every extra-claim equality. The fourth term gives `pointPolynomial` degree at
most 4. The concrete mask is the previous value plus `yx 28`, with the two
degree-27 univariates in coefficient cells 0–55. Its degree proof splits the
symbolic coefficient sum into two 28-cell sums and a zero remainder, then
uses the existing VDeg operations.

R0Z threads π through coefficients, quotient batching, OOD/opened symbols,
the honest prover and the payload maps. The `.extraClaim` coordinate is
disclosed and retained by `nonRound`; the tail enters the mask total and
round polynomials. `D13Order` is stated without a concrete instance.
`D12.MaskImage` and `hvzk_perfect_of_maskImage` retain their form with π
threaded. D15's `Good` was not added.

Two placement details avoid import cycles without changing the specified
definitions: `padC2Trace` moved unchanged from SemPad to SemView, and the
shared `libraWeight` is defined in SemView for `openingStmt`, with the
`R0P.Mask.libraWeight` abbreviation in MaskProtocol. Row-space `honestClaims`
and the semantic weights remain unchanged.

**Exact soundness accounting.** `B3_card` is 11,200 (formerly 8,400), the
gamma-group addend is 16,800 (formerly 14,000), and `B4_card` is 400
(formerly 300). `R0P.Mask.masked_opening_budget_exact`, adjacent to
`combined_fiat_shamir_masked`, records
`ε WideExact 0 = (336869026605739 + 16800) / (|E| - 1)` and
`ε WideExact 1 = 400 / |E|`. Thus the gamma numerator is exactly
336,869,026,622,539 and the opening union-bound increase is exactly
`2800 / (|E| - 1) + 100 / |E|`. The closed combined bound remains
`Qtot * ((1 + delta0) * (choose(9557,22) / choose(262144,22))) + κ Qtot`:
the existing q22 term still dominates the updated individual errors. No
other soundness term changed.

**Replay evidence.** All R0 sources were staged into `sources/R0/` on
`dombarker@100.108.41.90`, using the pinned
`/home/dombarker/project-offloads/aspis-fs-generic-20261006` workspace and its
compiled cache. Attempts **3282–3366** used `sh run2.sh N Module 7000 7`,
one module at a time under `/tmp/aspis-r0-lean.lock`, in dependency order.
The adapter uses MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0, and a 900 s
timeout. The reservation was 24 GiB populated plus this job's 7 GiB, below
55 GiB. Lean is v4.32.0; Mathlib is
`81a5d257c8e410db227a6665ed08f64fea08e997`.

There were 85 attempts: 78 successful distinct targets and seven local
elaboration failures, all preserved in [t1/evidence.json](t1/evidence.json).
The repairs were explicit dot/sum rewrites, `Finset.mem_map` reindexing with
Lambda kept locally irreducible, and definitional coefficient-function
equalities. No limit was raised. Failed elaboration logs contain Lean's own
placeholder diagnostics and option suggestions; no forbidden declaration,
proof escape or option was added to a source. Every changed Lean file has a
successful replay at its final SHA-256, and all host-staged hashes match.
No unchanged successful target was replayed. Total compiler wall time was
492.14 s; the longest module was 23.18 s; peak RSS was 7,042,772 KiB; every
attempt used zero swap and stayed below the resource/time limits.

| Final target | Attempt | Exit | Wall (s) | Peak RSS (KiB) | Swap |
| --- | ---: | ---: | ---: | ---: | ---: |
| `R0P/MaskAll` | 3365 | 0 | 2.76 | 6,805,328 | 0 |
| `R0Z/Z4Maps` | 3366 | 0 | 4.21 | 6,850,240 | 0 |

The required `#print axioms` results are exactly
`[propext, Classical.choice, Quot.sound]` for all three declarations:
`AspisR0.Opening.wideBinding` (3286),
`R0P.Mask.combined_fiat_shamir_masked` (3348, also final target 3365), and
`R0Z.D12.hvzk_perfect_of_maskImage` (3362). The JSON records every attempt's
target, exit, wall, RSS, swap, base revision, exact source hash and raw audit
output, plus the final source manifest and dependency order.

The final source scan is clean for the prohibited proof escapes/options;
no concrete row universe was introduced. `R0C/SemStatement.lean` and
`R0C/CircleRows.lean` are byte-for-byte unchanged. The commit contains Lean
sources, this LOG section and the evidence JSON; no binaries.

### Lead acceptance of T1 — D13′, D14′, D14″ replayed; decision D16 (2026-10-09)

**Verdict: accepted.** Reviewed as the diff `fcb570199 → 56872d637`
(`codex/t1-transport-libra-20261009`), landed on `v8-reference` as
`5ab6dcb5d` (cherry-picked on top of R-E4; the only conflict was this LOG's
tail, resolved by keeping the G_ref note and the worker's section in order).

Statements, checked line by line against D13′ items 1–6, D14′ items 1–7 and
D14″:

- `R0/OpeningDefinitions`: `Data.transport`, `Data.extraWeight`,
  `Data.extraClaims`; `coeffWeight π w j := w (π.symm j)` with
  `coeffWeight_add/smul/sum`, `dot_coeffWeight_left`,
  `dot_coeffWeight_indicator`; `discrepancy`, `inactiveDefect`, `weights`
  (`coeffWeight π (∑ κ^(j+1) • eqWeight + indicator) + κ^4 • extraWeight`),
  `claim` (`+ κ^4 * width29Batch extraClaims γ`), `extraDiscrepancy`,
  `extraDefect`, `pointPolynomial` with `monomial 4 (extraDefect …)`, `B3` with
  the extra-row clause (D14″), `B4` filtering on
  `pointDefect ≠ 0 ∨ extraDefect ≠ 0`. `eqWeight`, `indicator`, `claimPrime`,
  `qWeights`, `totalWeights`, B1, B2, B5–B7, V1, V2, `Accept` unchanged in text.
- `R0/BadSetBounds`: `B3_card ≤ 11200` (per-candidate 84 + 28 = 112, times
  `Lambda_card ≤ 100`), `B3_extra_outside`, `pointPolynomial_degree ≤ 4`,
  `pointPolynomial_extra_coeff`, `B4_card ≤ 400` (`union_bound … 4`),
  `B4_outside` giving both defects. `R0/Ledger`: grouped γ addend 16,800, B4
  400. `R0/Binding`: conclusion gains `∀ l, D.extraClaims l = dot D.extraWeight (t l)`
  and reads `v = ∑ r ∈ D.inactive, exactInitialMessageCurve t γ (D.transport r)`;
  the extra clause is closed by `B3_extra_outside` after `B4_outside`;
  `wideBinding` by `type_of%`.
- `R0FS/Protocol`: `Stmt.transport/extraWeight/extraClaims`, `data`, `Witness`
  with the `coeffWeight` clause and the extra clause; `ε E 0`, `ε E 1` updated;
  `Hypotheses.d3`/`accept_not_doomed` destructure the new conclusion, statements
  unchanged. `R0C/OpeningSamplerBounds`, `R0C/SlackDensity`, `R0C/V3/DuplexQ`:
  constants only. `R0C/SemStatement.lean`, `R0C/CircleRows.lean` byte-identical.
- `R0P/SemView`: `TypedContext.transport/extraClaims`; `coeffsOf`, `rowsOf`,
  `rowsEquiv`, `coeffsOf_padC2Trace`, `dot_coeffWeight_coeffsOf`, `LambdaRows`,
  `mem_LambdaRows`, `card_LambdaRows`, `LambdaRows_card ≤ 100`; `openingStmt`
  sets `transport`, `extraWeight := libraWeight α`, `extraClaims`. All
  semantic candidate quantifications use `LambdaRows x.transport`; the two glue
  theorems take `t := rowsOf … m` and carry `hyx` through `honestExtra`;
  `witness_baseTyped` descends through `coeffsOf`.
- `R0P/MaskProtocol`: `maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K`;
  `honestExtra π t α l := dot (libraWeight α) (coeffsOf π t l)`; `MaskDegree`
  quantified over `π` and `t`; `terminalZ`, `virtualPolyZ`, `maskTotal`,
  `sumcheckChecksZ` carry `yx`; `virtualPolyZ_total/vdeg/indDeg` keep their
  form. `R0P/MaskValue`: `libraTail`, `dot_libraWeight`, `libraTail_vdeg`,
  `maskClaimsR0 B y0 yx α := maskValue … + yx 28`, `maskClaimsR0_vdeg`.
  `R0P/MaskInstance`: `maskValueClaims := maskClaimsR0`,
  `masked_opening_budget_exact`. `decisionZ` passes `P.statement.extraClaims`.
- R0Z: `PayloadCell.extraClaim`, `coeffsLinear`, `extraLinear`
  (`dotLinear (libraWeight) ∘ coeffsLinear π ∘ proj c`), `extraCell`;
  `.ood` and `.opened` through `coeffsLinear π`; `openingWeights π ch` with
  `libraWeight (alpha ch)` and zero extra claims; `mask` gains
  `extraCell π B t a 28`; `HonestProver.transport`; `proverOutput` encodes
  `coeffsOf h.transport t`; `D13Order` stated, no instance; `D12.MaskImage`
  and `hvzk_perfect_of_maskImage` unchanged in form; `nonRound` retains the
  new coordinate by its catch-all clause. D15's `Good` not added.
- No theorem gained a hypothesis beyond the explicit `π`/`yx` arguments.

Two placement deviations are accepted as placement, not statement changes:
`padC2Trace` moved unchanged from `SemPad` to `SemView`, and `libraWeight` is
defined in `SemView` (`SemSource.libraWeight`) with the `R0P.Mask.libraWeight`
abbreviation, both to avoid an import cycle.

**Soundness constant.** `ε E 0 = (336869026605739 + 16800)/(|E| − 1)`,
`ε E 1 = 400/|E|`, recorded exactly by `masked_opening_budget_exact` (`rfl`).
The increase over the pre-T1 constant is exactly `2800/(|E|−1) + 100/|E|`
(≈ 2⁻²³⁶·⁵ + 2⁻²⁴¹·⁴ per query), both terms authorised (D14′ item 7, D14″). The
closed bound of `combined_fiat_shamir_masked` is textually unchanged because
its `max` is the q22 term. No other term changed.

**Evidence** (`t1/evidence.json`): attempts 3282–3366, 85 attempts, 78
distinct successful targets, 7 local elaboration failures repaired in source
and preserved; max wall 23.18 s; peak RSS 7,042,772 KiB under MemoryMax 7G;
swap 0 throughout; no unchanged target replayed; Lean v4.32.0, Mathlib
`81a5d257`. `#print axioms` for `wideBinding` (3286),
`combined_fiat_shamir_masked` (3348, 3365), `hvzk_perfect_of_maskImage`
(3362): `[propext, Classical.choice, Quot.sound]`. My own scan of the 38
changed Lean files finds no `sorry`/`axiom`/`native_decide`/`admit`/
`maxRecDepth`/`maxHeartbeats`; the `decide` occurrences are pre-existing small
numeral facts. No co-author trailer; no binaries.

**Gate G_ref status.** (S) is closed: the masked soundness statement now
carries D13′, D14′ and D14″ with its constant recorded. (P1) T2, (P2) ZF1 and
(P3) remain open and are **held**.

**Decision D16 — hold on all D14 follow-up work until the cost probe reports.**
The Rust PLAN's P1 decision already holds T2 and ZF1. D16 extends the hold to
**R-H** (Rust D14 in the reference prover/verifier: lane-28 h cells, fourth
weight row, 29 extra claims, terminal h-terms). Reason: if the probe shows no
configuration fits one transaction, R-H is wasted; if one fits, the D14 row's
cost is ≈ 56 E×K products and one 29-claim batch, which cannot change the
probe's answer. The Lean Codex is idle by decision. Order after the probe
reports a fit: T2 → R-H → ZF1 → P3, then the §8 steps the probe selected,
Lean-first.

### Lead decision D17 — exact Lean form of D14 (a) and D15; T2 split into T2a (issued) and T2b (2026-10-10)

**User direction (2026-10-10): T2 is issued now.** D16's hold therefore
covers R-H and ZF1 only. The cost probe P1′ continues in parallel.

**What is and is not in Lean today.** `R0Z.D12.MaskImage` still states D12's
clauses (i), (ii) (with π threaded by T1). D14 (a) restated them as (i′), (ii′)
through the payload bijection Ψ_ch, and D15 restricted them to `Good`. Neither
is in Lean. Z4c verified (i′), (ii′) numerically on 100/100 samples for the
Libra design; the Lean theorem is open. T2 is split so that every statement
downstream of that theorem is proved now, and the theorem itself gets a
lead-designed route afterwards.

**D17.1 — definitions (new module `R0Z/Shift.lean`, importing `R0Z.D12`).**
With `ch : Challenges K`, `α := alpha ch`, `η := ch.sem 14`, `pub := x.1`:

- `GoodAlpha (a : Fin 10 → K) : Prop := (∀ j, a j ≠ 0 ∧ a j ≠ 1) ∧ a 9 ≠ 1/2`;
  `Good ch := GoodAlpha (alpha ch)` (D15, verbatim).
- `round9Poly : Payload K →ₗ[K] K[X]`, the polynomial with coefficients
  `v (.semanticCoeff 9 i)`, `i : Fin 28`; `evalRound9 ch := (Polynomial.leval
  (alpha ch 9)).comp round9Poly`.
- `claimMask B a : Payload K →ₗ[K] K :=
  (∑ c : Fin 16, (maskFactors B a).c1 c • proj (.pointClaim 0 (castLE c))) +
  (maskFactors B a).explicitG • proj (.pointClaim 0 27) +
  (∑ c : Fin 10, (maskFactors B a).maskOnly c • proj (.pointClaim 0 ⟨16+c, _⟩)) +
  proj (.extraClaim 28)`, with
  `claimMask_apply : claimMask B a v = R0P.Mask.maskClaimsR0 B (fun c => v (.pointClaim 0 c)) (fun c => v (.extraClaim c)) a`.
- `Phi0 B ch : Payload K →ₗ[K] K := evalRound9 ch − claimMask B (alpha ch)` (Z4c's Φ₀).
- `dir : Payload K := roundInclusion (fun j i => if j = 9 then (X − C (1/2 : K)).coeff i.val else 0)`
  (D14's direction d(X) = X − ½ in round 9; zero elsewhere). Lemmas
  `evalRound9_dir : evalRound9 ch dir = alpha ch 9 − 1/2`, `claimMask_dir = 0`,
  `Phi0_dir : Phi0 B ch dir = alpha ch 9 − 1/2`, `nonRound_dir : nonRound dir = 0`.
- `originalOf pub B ch v : K := ch.sem 14 * terminalValue pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B (fun j c => v (.pointClaim j c)) (alpha ch)`
  (η·O read from a payload's three point claims; `terminalValue` reads lanes
  0–15 and 26 only, `Partition.lean` header).
- `shift pub B ch v := v + (originalOf pub B ch v * (alpha ch 9 − 1/2)⁻¹) • dir`,
  `unshift … := v − (…) • dir`; `originalOf_add_smul_dir : originalOf pub B ch (v + k • dir) = originalOf pub B ch v`
  (dir has no claim coordinate); `unshift_shift`, `shift_unshift`;
  `shiftEquiv pub B ch : Payload K ≃ Payload K`. This is Ψ_ch. It is defined
  for every `ch` through the field inverse; nothing below needs
  `alpha ch 9 ≠ 1/2` except the terminal-zero lemma `Phi0_sRem`.
- `sRem h B x w ch n : Payload K := roundInclusion (g h B x w ch n) − (Phi0 B ch (roundInclusion (g h B x w ch n)) * (alpha ch 9 − 1/2)⁻¹) • dir`
  (D14's s(w,n)); `cTilde h B x w ch : Payload K := c h B x w ch − (originalOf x.1 B ch (c h B x w ch) * (alpha ch 9 − 1/2)⁻¹) • dir`
  (D14's c̃(w)).
- `MaskImageOn (P : Challenges K → Prop) (h) (B) (x) : Prop :=
  (∀ ch, P ch → ∀ w n, h.public w = x.1 → sRem h B x w ch n ∈ LinearMap.range ((A h.transport B ch).comp inlM)) ∧
  (∀ ch, P ch → ∀ w w', h.public w = x.1 → h.public w' = x.1 → cTilde h B x w ch − cTilde h B x w' ch ∈ LinearMap.range (A h.transport B ch))`.
  **`MaskImageOn Good h B x` is the privacy obligation from now on** (D14 (a)
  with D15). `D12.MaskImage` and `hvzk_perfect_of_maskImage` stay as proved
  theorems about D12's wording; they are no longer the target.

**D17.2 — theorems of T2a (all routine: Lagrange, linearity, the existing
`vdeg_*` and `*_add_pure` lemmas).**

1. `rounds_eval_of_vdeg (ch) (j : Fin 10) (f) (hf : VDeg 10 (fun _ => 27) f) (z : K) :
   (rounds ch j f).eval z = ∑ tail : Fin (9−j.val) → Bool, f (roundPoint ch j z tail)`.
   Route: from `VDeg` (SemDeg.lean: the `∃ p, natDegree ≤ 27 ∧ ∀ x, p.eval x = G (cons x v)`
   clause, reached through the first nine coordinates), the map
   `z ↦ ∑ tail f (roundPoint ch j z tail)` is a polynomial of degree ≤ 27,
   and `Lagrange.eq_interpolate` on the 28 nodes `k : Fin 28` gives equality.
   Needed instance: `roundPoint ch 9 z tail = Function.update (alpha ch) 9 z`
   (`roundPoint_nine`).
2. `Phi0_A (t : T K F) : Phi0 B ch (A h.transport B ch t) = 0`. Route:
   `L_round` at j = 9, `rounds_eval_of_vdeg` with `maskClaimsR0_vdeg`
   (through `maskLinear_apply`), then `claimsLinear_apply`,
   `extraLinear_apply`, `claimMask_apply`. (Silent masks lie in `ker Φ₀`.)
3. `Phi0_roundInclusion_g : Phi0 B ch (roundInclusion (g h B x w ch n)) =
   originalOf x.1 B ch (payload h B x w ch (0,n)) − originalOf x.1 B ch (c h B x w ch)`.
   Route: `claimMask` vanishes on round-only payloads (definitional);
   `g = originalRounds (actual (0,n)) − originalRounds (actual 0)`;
   `rounds_eval_of_vdeg` at j = 9 with `vdeg_smul`/`vdeg_terminalValue`; the
   point claims of `payload … (0,n)` are `honestClaims (actual … (0,n)) α`
   by definition of `run`.
4. `Phi0_sRem (hgood : alpha ch 9 ≠ 1/2) : Phi0 B ch (sRem h B x w ch n) = 0`
   (linearity and `Phi0_dir`).
5. `payload_eq_shift (t : T K F) :
   payload h B x w ch t = shift x.1 B ch (cTilde h B x w ch + A h.transport B ch t + sRem h B x w ch t.2)`.
   Route: `D12.decomposition`; `originalOf_add_smul_dir`; the point claims of
   `payload … (m,n)` equal those of `payload … (0,n)` by `actual_add_pure`
   and `terminal_add_pure`; item 3; the three `(alpha ch 9 − 1/2)⁻¹`
   terms cancel identically, so no `Good` hypothesis.
6. `equalLaws_comp {R S V W} [Fintype R] [Fintype S] (Ψ : V → W) {f : R → V} {g : S → V}
   (h : EqualLaws f g) : EqualLaws (Ψ ∘ f) (Ψ ∘ g)` (from
   `LawTransport.mean_eq_of_equalLaws` with the indicator test).
7. `HVZK_on (P : Challenges K → Prop) h B outputs x : Prop :=
   ∀ (hx : InLanguage h x) w ch, P ch → h.public w = x.1 →
   EqualLaws (JointView.view h B outputs x w ch) (JointView.simulator h B outputs x hx ch)`;
   `hvzk_on_good : MaskImageOn Good h B x → HVZK_on Good h B outputs x`.
   Route: D12's proof with `payload_eq_shift` in place of `decomposition`:
   `AbsorptionLaw.mixture` with `g' n := sRem … n` (clause (i′)) gives
   `EqualLaws (fun t => cTilde + A t + sRem t.2) (fun t => cTilde + A t)`;
   `equalLaws_comp (shift …)`; `AffineLaw.equal_laws_of_mask_image` with
   clause (ii′); `equalLaws_comp` again; transport through `Partition.equiv`
   and `equal_laws_const_pair` exactly as in `hvzk_perfect_of_maskImage`.
8. Density (module `R0Z/GoodDensity.lean`, no protocol imports):
   `badAlpha_card : ((Finset.univ : Finset (Fin 10 → K)).filter (fun a => ¬ GoodAlpha a)).card ≤ 21 * Fintype.card K ^ 9`
   (union of 21 coordinate-fixing sets, each of card `|K|^9` by
   `Equiv.piFinSuccAbove`), and
   `badAlpha_density : (… .card : ℚ) / (Fintype.card K : ℚ) ^ 10 ≤ 21 / Fintype.card K`.
9. FS ledger (module `R0Z/FsGood.lean`, importing `R0Z.FsStatement` and
   `R0Z.Shift`): `badMass (P) (bridge : ROMBridge …) (adv) (x) : ℚ :=
   mean (fun coin => if P (bridge.draw adv x coin) then 0 else 1)`;
   `middle_means_close (hh : HVZK_on P h B outputs x) :
   |mean (middleReal …) − mean (middleIdeal …)| ≤ badMass P bridge adv x`
   (as `middle_means_eq` through `LawTransport.mean_product`; on coins with
   `P ch` the inner means are equal, otherwise they differ by at most 1
   because `bit` is 0/1-valued);
   `zkfs_of_hvzk_on (hh : HVZK_on P …) (hr : ROMReduction … ε_fs)
   (hmass : ∀ bridge adv, badMass P bridge adv x ≤ ε_bad) : ZK_FS … (ε_fs + ε_bad)`;
   `zkfs_of_maskImageOn_good : MaskImageOn Good h B x → ROMReduction … ε_fs →
   (∀ bridge adv, badMass Good bridge adv x ≤ ε_bad) → ZK_FS … (ε_fs + ε_bad)`.
   Identifying `ε_bad` with `21/|K_α|` is ZF1's obligation (it needs the FS
   draw's α-row law); item 8 is the count it will use. This is the Lean form
   of "statistical HVZK with the 21/|K_α| term": perfect on `Good`, plus one
   named ledger term.
10. `R0Z/Z4Maps.lean`: restate the two targets on `Good` and after Ψ_ch:
    `roundMask_surjectivity := ∀ ch, Good ch → ∀ w n, h.public w = x.1 →
    ∃ m : silentMasks …, silentRoundMaskMap … m = roundProjection (sRem h B x w ch n)`;
    `c1_surjectivity` unchanged except `∀ ch, Good ch →` (its C1 projection
    does not see `dir`). Props only, as before.

Nothing in T2a asserts `MaskImageOn Good`. No `sorry`, no axiom, no new
hypothesis on any existing theorem; `D12.lean` is not edited.

**D17.3 — T2b (route to be fixed by the lead after T2a lands; not issued).**
(i′) decomposes as (a) `sRem ∈ Chain₀ ch`, where `Chain₀ ch` is the
K-subspace of round-only payloads with zero initial sum, the nine
boundary-chain equalities at `alpha ch`, and zero terminal value at α₉
(269 K-dimensions = Z4c's 1076 over M31), proved from the honest sumcheck
identities of `rounds` (Lagrange, as in item 1) and `Phi0_sRem`; and (b)
`Chain₀ ch ⊆ roundProjection (silent image)` on `Good`, proved by an explicit
spanning family of silent masks built as Z4c's lifts (a kernel tape in a
mask-only lane or G paired with `−γ^(c−28)·t` in D so the batched word is
zero; the Libra cells of D for rounds 8–9), hitting each round-j monomial
X^d after normalisation; the family's rank depends on `α_j(1−α_j) ≠ 0`,
which is why `Good` is the hypothesis. (ii′) decomposes as the C1
encoder-restriction statement (`c1_surjectivity`, structural under D13: the
eligible restriction and the full restriction have the same image at every
fibre set) plus a compatible lift of the remaining components. T2b will be
several Lean jobs; each gets its own numbered statement before issue.

**Job T2a (Lean Codex).** Base: the `origin/v8-reference` head carrying this
section. Branch `codex/t2a-shift-good-20261010`. New modules
`R0Z/Shift.lean`, `R0Z/GoodDensity.lean`, `R0Z/FsGood.lean`; edit
`R0Z/Z4Maps.lean` (item 10) only. No R0P/R0/R0FS/R0C edit; `D12.lean`
untouched. Replay on the host from attempt 3367, one module at a time; final
targets `R0Z/FsGood` and `R0Z/Z4Maps`; `#print axioms` for `payload_eq_shift`,
`Phi0_A`, `Phi0_sRem`, `hvzk_on_good`, `badAlpha_density`, `zkfs_of_hvzk_on`,
`zkfs_of_maskImageOn_good`. Stop list: any statement differing from D17.1–D17.2
(report the exact mismatch and stop); any proof of items 1–9 needing more
than Lagrange interpolation, linearity, `VDeg` unfolding and the named
existing lemmas; any attempt to prove or assume `MaskImageOn Good`; any
module above the cap or 900 s; `sorry`/`axiom`/`native_decide`/`admit`/
`maxRecDepth`/`maxHeartbeats`; concrete `Finset.univ` over rows, states or
`Fin 262144`; any edit outside the four files named.

### Lead amendment D17′ — placement of `GoodAlpha` (T2a stop resolved, 2026-10-10)

The T2a worker stopped before editing: D17.1 places `GoodAlpha` in
`R0Z/Shift.lean` (which imports `R0Z.D12`), while D17.2 item 8 requires
`R0Z/GoodDensity.lean` to state `badAlpha_card`/`badAlpha_density` about
that same declaration with Mathlib as its only import. Correct. Amendment:
`GoodAlpha (a : Fin 10 → K) : Prop := (∀ j, a j ≠ 0 ∧ a j ≠ 1) ∧ a 9 ≠ 1/2`
is defined in `R0Z/GoodDensity.lean` (namespace `R0Z.Shift`, over
`{K : Type} [Field K]`, so the name is the one D17.1 uses), and
`R0Z/Shift.lean` imports `R0Z.GoodDensity` and defines `Good ch := GoodAlpha
(alpha ch)` there. Type and body unchanged; no duplicate declaration. Everything
else in D17 and the T2a job stands; T2a is re-issued on the head carrying this
section.

### Lead acceptance of Z5 (`z4/FINDINGS-Z5.md`); decision D18 — the R1 transport (2026-10-11)

**Verdict: accepted as computation.** Z5 (`codex/z5-digit-transport-20261010`
@ `ce904954b`, cherry-picked here) tested all 120 digit-position permutations
τ with identity digit maps against Z4c's C1 criterion (rank 112 for every one
of the 16 semantic columns on the random 22-fibre set and on {0,…,21}, all 20
challenge vectors, fourth weight row included). Three pass: τ = [3,4,2,0,1],
[4,2,3,0,1], [4,3,2,0,1]; all 117 others fail first at column 0 on the
consecutive set (ranks 54–111). Controls: identity π fails on the consecutive
set exactly as Z4a found (ranks 80–99); D13's π passes. The first pass was run
through Z4c's full gate: silent rank 1,076 on every vector, initial-retained
and conditioned rank 1,080, (i′) 100/100, (ii′) 100/100, derivative diagnostic
100/100, empty excess supports, all 20 challenge records and 100 terminal
diagnostics identical to `probe-C.log`. Receipts: gate 1,235.5 s, peak child
RSS 39,704 KiB, cgroup 51.8 MiB, swap 0, caps 3G/4G; 203 compiled-source
hashes verified; elimination routines byte-identical to the base; two staging
failures preserved and repaired; no Lean or production Rust change; no
binaries; no trailer. Stages 2–3 of the search were not run (the user agreed
to stop after the first exhaustive stage); nothing in R1 needs them.

**Decision D18 — the R1 transport.** For R1 the transport is the fixed digit
permutation
```
π_R1(r) = digit₃(r) + 4·digit₄(r) + 16·digit₂(r) + 64·digit₀(r) + 256·digit₁(r)
```
(base-4 digits of the row index, least significant first; coefficient digit d
takes row digit τ(d) with τ = [3,4,2,0,1]; all σ_d identity). Consequences:
1. Every weight the R1 verifier evaluates stays in product form over the five
   coefficient digits: `eq(α, π_R1⁻¹ j) = ∏_d eq₂(α-bit-pair τ(d), digit_d(j))`,
   the OOD weights `N_j(z)` are already digit-structured, the inactive
   indicator and the Libra row are 0/1 and sparse. The dual folds of all
   weights cost O(1) per constraint; the 3.5M "transport" component of R-E4's
   V2 disappears by construction.
2. D13's π (89 pads to the front) and `D13Order` remain R0's; R1's Lean states
   `π_R1` as an explicit `Equiv` built from the digit permutation (no
   generating rule, no order clause). The privacy rank property that D13 was
   reinstated for holds for π_R1 on the Z4c vectors by this computation; its
   structural proof belongs to T2b clause (ii′) and is expected to be simpler
   for a digit permutation than for D13's.
3. P2's variant S uses π_R1 (its placeholder was cost-equivalent; the probe
   should now be the design). The semantic layer, the mask and the fourth
   weight row are unaffected: the Libra weight is coefficient-indexed with no
   transport, as D14′ states.
4. The two other passing τ are recorded as alternates; the choice among the
   three is cost-neutral and is not revisited unless T2b needs it.

Half of the fit gate (PLAN, 2026-10-10 decision) is passed. The other half is
P2's variant S fitting two transactions with ≥ 0.2M headroom each.
### T2a completed — D17 shift Ψ_ch, `Good`, statistical HVZK ledger term (2026-10-11)

Implemented D17.1, D17.2 items 1–10 and the D17′ placement on
`codex/t2a-shift-good-20261010`, based on
`bb44131caf6293417602b74655a77081e05143b1`. Three new modules and one edit:
`R0Z/GoodDensity.lean` (Mathlib only), `R0Z/Shift.lean` (imports `R0Z.D12`,
`R0Z.GoodDensity`, `R0Z.LawTransport`), `R0Z/FsGood.lean` (imports
`R0Z.FsStatement`, `R0Z.Shift`), and `R0Z/Z4Maps.lean` (item 10 only; it now
imports `R0Z.Shift`). No R0P/R0/R0FS/R0C file and no other R0Z file changed;
`D12.lean` is untouched. Nothing proves, assumes or weakens `MaskImageOn Good`.

**Placements.** `GoodAlpha` is in `R0Z/GoodDensity.lean`, namespace
`R0Z.Shift`, over `{K : Type} [Field K]` (D17′); `Good ch := GoodAlpha (alpha ch)`
is in `R0Z/Shift.lean`. Items 1–7 are in `R0Z.Shift`, item 8 in
`R0Z.Shift` (GoodDensity), item 9 in namespace `R0Z.FsGood`, item 10 in
`R0Z.Z4Maps`. Two representation details, neither a statement change:
`dir` is written with `PayloadSplit.roundInclusion` (the K-linear map whose
`restrictScalars F` is `D12.roundInclusion`; the two agree as functions, and
`nonRound_dir` is proved by the same `cases coord <;> rfl` as D12's lemma),
while `sRem` uses `D12.roundInclusion (F := F)` exactly as `decomposition`
does; and the `Equiv.piFinSuccAbove` named in item 8 is `Fin.insertNthEquiv`
in Mathlib `81a5d257` — the bijection is built from its two components
`Fin.insertNth`/`Fin.removeNth` with `insertNth_apply_same`,
`insertNth_self_removeNth`, `removeNth_insertNth`.

**Statements (D17.1).** `GoodAlpha a := (∀ j, a j ≠ 0 ∧ a j ≠ 1) ∧ a 9 ≠ 1/2`;
`Good ch := GoodAlpha (alpha ch)`. `round9Poly : Payload K →ₗ[K] K[X] :=
∑ i : Fin 28, (monomial i.val).comp (proj (.semanticCoeff 9 i))` with
`round9Poly_apply`; `evalRound9 ch := (Polynomial.leval (alpha ch 9)).comp round9Poly`.
`claimMask B a` is the displayed sum of `proj (.pointClaim 0 _)` reads plus
`proj (.extraClaim 28)`, with `claimMask_apply : claimMask B a v =
R0P.Mask.maskClaimsR0 B (fun c => v (.pointClaim 0 c)) (fun c => v (.extraClaim c)) a`.
`Phi0 B ch := evalRound9 ch - claimMask B (alpha ch)`. `dir := roundInclusion
(fun j i => if j = 9 then (X - C (1/2 : K)).coeff i.val else 0)` with
`evalRound9_dir : evalRound9 ch dir = alpha ch 9 - 1/2`, `claimMask_dir = 0`,
`Phi0_dir : Phi0 B ch dir = alpha ch 9 - 1/2`, `nonRound_dir : nonRound dir = 0`.
`originalOf pub B ch v := ch.sem 14 * terminalValue pub (ch.sem 0) (ch.sem 1)
(ch.sem 2) (ch.sem 13) (zc ch) B (fun j c => v (.pointClaim j c)) (alpha ch)`;
`shift pub B ch v := v + (originalOf pub B ch v * (alpha ch 9 - 1/2)⁻¹) • dir`,
`unshift` with `-`; `originalOf_add_smul_dir`, `originalOf_sub_smul_dir`,
`unshift_shift`, `shift_unshift`, `shiftEquiv : Payload K ≃ Payload K`.
`sRem h B x w ch n := roundInclusion (g h B x w ch n) - (Phi0 B ch (roundInclusion
(g h B x w ch n)) * (alpha ch 9 - 1/2)⁻¹) • dir`; `cTilde h B x w ch := c h B x w ch -
(originalOf x.1 B ch (c h B x w ch) * (alpha ch 9 - 1/2)⁻¹) • dir`.
`MaskImageOn P h B x := (∀ ch, P ch → ∀ w n, h.public w = x.1 → sRem h B x w ch n ∈
LinearMap.range ((A h.transport B ch).comp inlM)) ∧ (∀ ch, P ch → ∀ w w',
h.public w = x.1 → h.public w' = x.1 → cTilde h B x w ch - cTilde h B x w' ch ∈
LinearMap.range (A h.transport B ch))`.

**Theorems (D17.2).**
1. `rounds_eval_of_vdeg (ch) (j) (f) (hf : VDeg 10 (fun _ => 27) f) (z) :
   (PayloadSplit.rounds ch j f).eval z = ∑ tail : Fin (9-j.val) → Bool, f (roundPoint ch j z tail)`.
   Route as specified: `vdeg_update` extracts the coordinate-`j` univariate of
   degree ≤ 27 from `VDeg` by induction through the leading coordinates
   (`Fin.cons_update`, `Fin.update_cons_zero`, `Fin.cons_self_tail`);
   `roundPoint_update` rewrites the round point as `Function.update`; the
   tail-sum polynomial has `natDegree < 28` (`natDegree_sum_le_of_forall_le`);
   `Lagrange.eq_interpolate` on the 28 nodes and
   `Lagrange.interpolate_eq_of_values_eq_on` close it. Node injectivity
   (`nodes_injOn`) is derived from the ambient `[Algebra (ZMod P) K]` exactly as
   `R0P.SemD3Glue.semE_charP` does (`charP_of_injective_algebraMap`, then
   `CharP.natCast_injOn_Iio` with `28 ≤ P` by `norm_num`); no hypothesis was
   added to the statement. `roundPoint_nine : roundPoint ch 9 z tail =
   Function.update (alpha ch) 9 z`; `eval_rounds_nine : (rounds ch 9 f).eval
   (alpha ch 9) = f (alpha ch)`.
2. `Phi0_A (h) (B) (ch) (t : T K F) : Phi0 B ch (A h.transport B ch t) = 0`, through
   `Phi0_L` on `PayloadSplit.L`: `L_round`, `sum_monomial_coeff` (a polynomial
   of `natDegree < 28` is the sum of its 28 monomials, `as_sum_range'`),
   `eval_rounds_nine` with `maskClaimsR0_vdeg` transported through
   `maskLinear_apply`, and `claimsLinear_apply`/`extraLinear_apply`/`claimMask_apply`.
3. `Phi0_roundInclusion_g : Phi0 B ch (roundInclusion (g h B x w ch n)) =
   originalOf x.1 B ch (payload h B x w ch (0,n)) - originalOf x.1 B ch (c h B x w ch)`:
   `claimMask_roundInclusion` (definitional zero), `g` as a difference of
   `originalRounds`, `vdeg_smul`/`vdeg_terminalValue`, `eval_rounds_nine`;
   `payload_pointClaim` and `originalOf_payload` are `rfl`, and `originalOf_c`
   uses D12's `map_zero Partition.equiv` identification of `c` with `payload 0`.
4. `Phi0_sRem (hgood : alpha ch 9 ≠ 1/2) : Phi0 B ch (sRem h B x w ch n) = 0`
   (linearity, `Phi0_dir`, `inv_mul_cancel₀`).
5. `payload_eq_shift (t : T K F) : payload h B x w ch t = shift x.1 B ch (cTilde h B x w ch +
   A h.transport B ch t + sRem h B x w ch t.2)`, with no `Good` hypothesis:
   `decomposition`, `originalOf_payload_pure` (`actual_add_pure`,
   `terminal_add_pure`), item 3, `add_smul`, `abel`, then
   `originalOf_sub_smul_dir` and `sub_add_cancel`.
6. `equalLaws_comp {R S V W} [Fintype R] [Fintype S] (Ψ : V → W) {f g} (h : EqualLaws f g) :
   EqualLaws (Ψ ∘ f) (Ψ ∘ g)` from `LawTransport.mean_eq_of_equalLaws` with the
   indicator test.
7. `HVZK_on P h B outputs x := ∀ (hx : InLanguage h x) w ch, P ch → h.public w = x.1 →
   EqualLaws (JointView.view h B outputs x w ch) (JointView.simulator h B outputs x hx ch)`;
   `hvzk_on_good : MaskImageOn Good h B x → HVZK_on Good h B outputs x`, following
   `D12.hvzk_perfect_of_maskImage` with `payload_law_on` (`AbsorptionLaw.mixture`
   on `sRem`, `equalLaws_comp (shift …)`, `payload_eq_shift`) in place of
   `payload_law`, `AffineLaw.equal_laws_of_mask_image` on `cTilde`,
   `equalLaws_comp (shift …)` again, then `equal_laws_of_equiv Partition.equiv`
   and `equal_laws_const_pair` verbatim.
8. `badAlpha_card : ((Finset.univ : Finset (Fin 10 → K)).filter (fun a => ¬ GoodAlpha a)).card ≤
   21 * Fintype.card K ^ 9` (21 pinned sets, `card_pinned : (pinned j c).card =
   Fintype.card K ^ 9` through `pinnedEquiv`, `Finset.card_biUnion_le`,
   `Finset.card_union_le`) and `badAlpha_density : (… .card : ℚ) / (Fintype.card K : ℚ) ^ 10 ≤
   21 / Fintype.card K`.
9. `badMass P bridge adv x := mean (fun coin => if P (bridge.draw adv x coin) then 0 else 1)`;
   `middle_means_close (hh : HVZK_on P h B outputs x) : |mean (middleReal …) − mean (middleIdeal …)|
   ≤ badMass P bridge adv x` (`mean_product` twice, `mean_sub`, `abs_mean_le`,
   `mean_le_mean`; on good coins `mean_eq_of_equalLaws`, otherwise both inner
   means lie in [0,1] because `bit` is 0/1-valued); `zkfs_of_hvzk_on (hh) (hr :
   ROMReduction … ε_fs) (hmass : ∀ bridge adv, badMass P bridge adv x ≤ ε_bad) :
   ZK_FS … (ε_fs + ε_bad)`; `zkfs_of_maskImageOn_good : MaskImageOn Good h B x →
   ROMReduction … ε_fs → (∀ bridge adv, badMass Good bridge adv x ≤ ε_bad) →
   ZK_FS … (ε_fs + ε_bad)`. Identifying `ε_bad` with `21/|K_α|` remains ZF1's.
10. `Z4Maps.roundMask_surjectivity := ∀ ch, Good ch → ∀ w n, h.public w = x.1 →
    ∃ m : silentMasks …, silentRoundMaskMap … m = roundProjection (sRem h B x w ch n)`;
    `c1_surjectivity` gains only `∀ ch, Good ch →`. Both remain `Prop`s.

**Replay evidence.** Before the first attempt the SHA-256 of all 100 worktree
`R0Z/*.lean` and `R0P/*.lean` sources matched the staged copies in
`sources/R0Z` and `sources/R0P` on `dombarker@100.108.41.90`, pinned workspace
`/home/dombarker/project-offloads/aspis-fs-generic-20261006` with its compiled
cache. Attempts **3367–3376** used `sh run2.sh N Module 7000 7`, one module at
a time, in the order GoodDensity → Shift → FsGood → Z4Maps (Z4Maps depends on
Shift only and was replayed before the FsGood repair). The adapter uses
MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0 and a 900 s timeout; the
reservation printed by the launcher was 24–26 GiB populated plus this job's
7 GiB. Lean is v4.32.0 (commit `8c9756b2`); Mathlib is `81a5d257`. Attempt
3367 did not compile: it was wrapped in an outer `flock` on the lock that
run2.sh already takes internally, deadlocked, and was killed after about ten
minutes with an empty `out-3367.log` and no time log; it is kept in the
record and the number was not reused.

| Attempt | Target | Exit | Wall (s) | Peak RSS (KiB) | Swap | Result |
| ---: | --- | ---: | ---: | ---: | ---: | --- |
| 3367 | `R0Z/GoodDensity` | — | — | — | — | launch deadlock, no compile |
| 3368 | `R0Z/GoodDensity` | 1 | 3.85 | 6,664,236 | 0 | 3 elaboration errors |
| 3369 | `R0Z/GoodDensity` | 1 | 3.18 | 6,689,372 | 0 | 2 elaboration errors |
| 3370 | `R0Z/GoodDensity` | 1 | 3.36 | 6,688,828 | 0 | 1 elaboration error |
| 3371 | `R0Z/GoodDensity` | 0 | 3.12 | 6,717,604 | 0 | green |
| 3372 | `R0Z/Shift` | 1 | 10.46 | 6,870,664 | 0 | elaboration errors |
| 3373 | `R0Z/Shift` | 0 | 7.48 | 6,880,060 | 0 | green |
| 3374 | `R0Z/FsGood` | 1 | 3.06 | 6,821,240 | 0 | 1 elaboration error |
| 3375 | `R0Z/Z4Maps` | 0 | 3.77 | 6,852,540 | 0 | green (final target) |
| 3376 | `R0Z/FsGood` | 0 | 3.17 | 6,857,500 | 0 | green (final target) |

The repairs were: beta-reducing `change`s and the explicit dependent family
`(α := fun _ => K)` for `Fin.insertNth`/`removeNth`; explicit set arguments so
`Finset.card_union_le`'s `DecidableEq` instance is determined;
`Nat.add_le_add_right` for the summand order; `div_eq_div_iff` + `ring` for the
density identity; qualifying `PayloadSplit.rounds` and importing
`R0Z.LawTransport`; a `Payload K` ascription on `dir`; two rewrites whose
motive was not type correct because of `↑(9 : Fin 10)` in dependent positions,
replaced by `dif_pos` on a hypothesis stated at `(9 : Fin 10).val` and by
`Fin.elim0 (Fin.cast h0 i)`; `PayloadSplit.L` reads by `simp only
[PayloadSplit.L, LinearMap.pi_apply, …]` with `claimsLinear extraLinear
dotLinear honestClaims` locally irreducible (the PayloadSplit pattern) instead
of `change`; an explicit `originalRounds_eq` rewrite; and naming the cast in
`abs_of_nonneg`. Failed logs contain Lean's own recursion-depth diagnostic
text; no `maxRecDepth`, `maxHeartbeats`, `sorry`, `axiom`, `native_decide`,
`admit` or `decide` appears in any source, and no limit was raised. Total
compiler wall time was 41.45 s over the nine compiled attempts; the longest
module was 10.46 s; peak RSS was 6,880,060 KiB; every attempt used zero swap.
Every changed Lean file has a successful replay at its final SHA-256 and all
four staged hashes match the worktree.

The required `#print axioms` results are exactly
`[propext, Classical.choice, Quot.sound]` for `payload_eq_shift`, `Phi0_A`,
`Phi0_sRem`, `hvzk_on_good` (3373), `badAlpha_density` (3371; also
`badAlpha_card`, `card_pinned`), `zkfs_of_hvzk_on`, `zkfs_of_maskImageOn_good`
(3376; also `middle_means_close`), together with `rounds_eval_of_vdeg`,
`Phi0_roundInclusion_g`, `equalLaws_comp` (3373) and the three Z4Maps maps
(3375). `GoodAlpha`, a definition, reports `[propext, Quot.sound]`. The source
scan finds `Finset.univ` only over `Fin 10`, `Fin 10 → K`, the 28 Lagrange
nodes and the bridge coin type; no row, state or `Fin 262144` universe is
evaluated. Per-attempt data, raw audit lines, caps, toolchain lines and the
final source manifest are in [t2a/evidence.json](t2a/evidence.json). The
commit contains the four Lean sources, this LOG section and the evidence JSON;
no binaries.

### Lead acceptance of T2a (2026-10-11)

**Verdict: accepted.** `codex/t2a-shift-good-20261010` @ `6eef05520`
(cherry-picked here; the only conflict was this LOG's tail, resolved by
keeping the D18 section and then the worker's section). Reviewed line by
line against D17.1, D17.2 items 1–10 and D17′:

- `R0Z/GoodDensity.lean` (Mathlib only): `GoodAlpha` verbatim; `badAlpha_card
  ≤ 21·|K|⁹` by 21 coordinate-pinning sets each in bijection with `Fin 9 → K`
  (`Fin.insertNth`/`removeNth`, the components of what Mathlib now calls
  `Fin.insertNthEquiv`); `badAlpha_density ≤ 21/|K|`. No field element is
  enumerated.
- `R0Z/Shift.lean`: `Good`, `round9Poly`, `evalRound9`, `claimMask` (+
  `claimMask_apply` to `maskClaimsR0`), `Phi0`, `dir` (through
  `PayloadSplit.roundInclusion`, the same function as D12's restricted one),
  `evalRound9_dir`, `claimMask_dir`, `Phi0_dir`, `nonRound_dir`,
  `originalOf`, `shift`/`unshift`/`shiftEquiv`, `originalOf_add_smul_dir`,
  `sRem`, `cTilde`, `MaskImageOn` — each with D17.1's type and body. Items
  1–7: `rounds_eval_of_vdeg` (general z; node distinctness derived from the
  ambient `ZMod P` algebra, so no new hypothesis), `roundPoint_nine`,
  `Phi0_A`, `Phi0_roundInclusion_g`, `Phi0_sRem` (needs only
  `alpha ch 9 ≠ 1/2`), `payload_eq_shift` (no `Good` hypothesis, as
  predicted), `equalLaws_comp`, `HVZK_on`, `hvzk_on_good` (D12's proof shape
  with the shift). Nothing asserts, assumes or weakens `MaskImageOn Good`.
- `R0Z/FsGood.lean`: `badMass`, `middle_means_close`, `zkfs_of_hvzk_on`,
  `zkfs_of_maskImageOn_good` as D17.2 item 9.
- `R0Z/Z4Maps.lean`: both targets on `Good`, the round target on
  `roundProjection (sRem …)` (item 10). `D12.lean` and every R0P/R0/R0FS/R0C
  file untouched.
- Scan: no `sorry`/`axiom`/`native_decide`/`admit`/`maxRecDepth`/
  `maxHeartbeats`/`decide`; `Finset.univ` only over `Fin 10`, `Fin 28`,
  `Fin 10 → K` (symbolically) and the bridge coin type.

**Evidence** (`t2a/evidence.json`): attempts 3367–3376; 3367 never compiled
(my prompt wrapped the launcher in an outer `flock` on the lock `run2.sh`
already takes; killed after ten minutes, number not reused — a prompt
defect, recorded); 3368–3370 and 3372, 3374 were elaboration failures
repaired in source; final targets `R0Z/GoodDensity` 3371, `R0Z/Shift` 3373,
`R0Z/Z4Maps` 3375, `R0Z/FsGood` 3376, all exit 0; max wall 10.46 s; peak RSS
6,880,060 KiB under MemoryMax 7G; swap 0; no cap raised; the 100 staged
unchanged R0Z/R0P sources were hash-checked against the worktree first.
`#print axioms` exactly `[propext, Classical.choice, Quot.sound]` for
`payload_eq_shift`, `Phi0_A`, `Phi0_sRem`, `hvzk_on_good`,
`rounds_eval_of_vdeg`, `Phi0_roundInclusion_g`, `equalLaws_comp`,
`badAlpha_card`, `badAlpha_density`, `middle_means_close`,
`zkfs_of_hvzk_on`, `zkfs_of_maskImageOn_good`. No trailer, no binaries.

**Where privacy stands.** The chain is now
`MaskImageOn Good h B x → HVZK_on Good → ZK_FS (ε_fs + badMass Good)`, all
proved; `badAlpha_density` is the count ZF1 will use to pin `badMass Good`
to `21/|K_α|` from the FS draw's α-row law. The one open theorem is
`MaskImageOn Good` (T2b, route D17.3). Its first job needs one fact I have
not located in the trees: that the honest original's hypercube total is
unchanged by eligible noise (so that `g`'s initial sum vanishes and `sRem`
lies in the chain-consistent, terminal-zero space). A read-only check of the
completeness facts available in R0P/R0Z is running; T2b-1 is specified when
it reports. These results carry over to R1 unchanged (the mask and round
analysis is PCS-independent).

### Lead acceptance of Z6 (`z4/FINDINGS-Z6.md`); T2b-1 specified and HELD (2026-10-11)

**Accepted as computation.** Z6 (`codex/z6-noise-rows-20261011`,
cherry-picked here) shows on all 1,000 (witness, tape, challenge-prefix)
combinations that the original terminal is unchanged by eligible noise **at
every Boolean row**, that `balance` (row 1023) and the helper (H1) are
invisible to every terminal row, and it derives the rule from source for the
2,736 Poseidon padding cells (read only through terms whose selector weight
is identically 0); the remaining 1,067 eligible cells in rows 912–1023 pass a
randomized dependence test (miss probability ≈ 25/2³¹ per test) but were not
audited from source. Receipts: own scopes 3G/4G/swap 0, no cap raised, 204
source hashes verified, one preflight assertion failure retained. This is
exactly the fact the T2a acceptance said was missing: the remainder g has
zero initial sum because each honest original row is noise-invariant, so
clause (i′) is not false for the reason I feared.

**Why the Lean form is an audit, not a definition.** `eligible c r`
(`R0Z/MaskLayout.lean:38–42`) is an explicit cell list (local rows 13–15
below 912; rows ≥ 912 not used by `forestPathUsed`/`pairAuxUsed`), not "not
read by any lane". So the Lean fact must be proved family by family, in the
style of `HelperInvariant.helper_eligible` (`row_values_eligible` with
`protected_registry`), which already does it for the helper's reads.

**Job T2b-1 (Lean; HELD until the user decides whether the privacy work
continues as research).** Base: the head carrying this section. New module
`R0Z/TerminalEligible.lean` and additions to `R0Z/Shift.lean`
(or a new `R0Z/Chain.lean`); `D12.lean`, `Shift.lean`'s existing statements
and all R0P/R0/R0FS/R0C files untouched.

1. **Lemma A (noise invariance of the original rows).**
   `terminal_row_eligible (pub) (t : Trace K) (e : EligibleNoise K F) (ch) (b : Fin 10 → Bool) :
   terminalValue pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B
     (honestClaims (prepare pub (applyEligible t e) ch) (ofBool b)) (ofBool b) =
   terminalValue … (honestClaims (prepare pub t ch) (ofBool b)) (ofBool b)`.
   Route: `honestClaims` at a Boolean point reads `rowOpenings` (existing
   `honestClaims_ofBool`/`honestRows`); lane 26 by `helper_eligible`; for
   C1 lanes, every cell that `laneAt … (rowOpenings u b)` reads with a
   nonzero coefficient at a Boolean row is non-eligible and ≠ 1023 —
   proved per family from the Copy*/LogUp*/Positivity*/Path/Value/Digest/
   Asset/Schedule/Occupancy definitions, the Poseidon padding case by the
   selector-weight argument in FINDINGS-Z6. Also `applyAff_zero :
   applyAff B u 0 = u` (or the terminal-level equivalent), so that
   `actual … (0,n)` and `actual … 0` differ only by the noise tape.
   Stop list: any family whose reads cannot be shown non-eligible from its
   definition (report the family, the cell and the row).
2. **Lemma B (honest sumcheck identities of `rounds`).** For
   `VDeg 10 (fun _ => 27) f`: `rounds_initial : (rounds ch 0 f).eval 0 +
   (rounds ch 0 f).eval 1 = bsumB 10 f` and `rounds_chain (j : Fin 9) :
   (rounds ch j.succ f).eval 0 + (rounds ch j.succ f).eval 1 =
   (rounds ch j.castSucc f).eval (alpha ch j.castSucc)`. Route:
   `rounds_eval_of_vdeg` plus `roundPoint` lemmas re-indexing the Boolean
   tail with `Fin.cons` against `bsumB`'s leading-coordinate recursion
   (`Zerocheck.lean`).
3. **`Chain0 ch : Submodule K (Payload K)`**: payloads v with
   `nonRound v = 0`, `p₀ᵛ(0) + p₀ᵛ(1) = 0`, `p_{j+1}ᵛ(0) + p_{j+1}ᵛ(1) =
   p_jᵛ(α_j)` for j = 0..8, and `p₉ᵛ(α₉) = 0`, where `p_jᵛ` is the round-j
   polynomial read from the `.semanticCoeff j ·` cells (generalise
   `round9Poly` to `roundPoly j`). All conditions are K-linear.
4. **`sRem_mem_chain0 (hgood : alpha ch 9 ≠ 1/2) : sRem h B x w ch n ∈ Chain0 ch`.**
   Initial sum: `g`'s two `originalRounds` have initial sums
   `η · bsumB 10 (fOrig … (actual … (0,n)))` and `η · bsumB 10 (fOrig … (actual … 0))`,
   equal by Lemma A row by row; chain by Lemma B for each, hence for the
   difference, and `dir` is chain-consistent (rounds 0–8 zero, p₉ = X − ½);
   terminal by `Phi0_sRem` and `claimMask_roundInclusion`; `nonRound` by
   `nonRound_dir` and the round-only shape of `g`.
   Replay on the host from attempt 3377, one module at a time, final target
   the new module(s); `#print axioms` for `terminal_row_eligible`,
   `rounds_initial`, `rounds_chain`, `sRem_mem_chain0`; standard caps and
   stop list; nothing may assume or weaken `MaskImageOn Good`.

**After T2b-1: T2b-2** is the spanning half — `Chain0 ch ⊆ roundProjection
(silent image)` on `Good` — from Z4c/Z5's lift family; its statement is
written when T2b-1 lands. Both are research under the current verdict
(PLAN, 2026-10-11): R0 and R1 have no deployment path; v7 stands.

### User direction (2026-10-12): privacy continues as research — T2b-1 released; T2b-2a specified

The user: "let's get privacy all the way through". The hold on T2b-1 (section
above) is lifted; T2b-1 is issued as written there, attempts from 3377. The
remaining sequence is T2b-2a (below) → T2b-2b (the spanning argument;
statement written when 2a lands) → ZF1 (the ROM reduction and the `badMass
Good ≤ 21/|K_α|` identification) → the closed privacy theorem for R0. One
Lean job at a time on the host; the deployment verdict (PLAN, 2026-10-11)
is unchanged.

**Job T2b-2a (Lean; issued after T2b-1 lands).** Closed forms for pure-mask
round images and the easy inclusion. New module `R0Z/PureRounds.lean`
(imports `R0Z.Shift` and T2b-1's module); nothing else edited.

1. **Easy inclusion.** `silent_mem_chain0 (m : M K F)
   (hs : nonRound (F := F) ((A h.transport B ch).comp inlM m) = 0) :
   (A h.transport B ch).comp inlM m ∈ Chain0 ch`. Route: the `.maskSum`
   coordinate of `L (pureTrace m)` is `∑ bits, maskLinear π B (ofBool bits) (pureTrace m)`
   and `rounds_initial` (T2b-1 Lemma B) identifies it with `p₀(0)+p₀(1)`,
   so silence gives zero initial sum; `rounds_chain` for
   `f := fun a => maskLinear π B a (pureTrace m)` (`maskLinear_vdeg`);
   terminal by `Phi0_A` with `claimMask (A (m,0)) = 0` from silence
   (`claimMask` reads only `.pointClaim 0 ·` and `.extraClaim 28`, which
   `nonRound` retains).
2. **Closed form for a mask-only lane.** With `w j := (3 + 22*j : K)` (the
   coefficients of `maskLinear 0`), `e_c := maskOnlyFactorExponent c`,
   `τ_c := towerBasis B ⟨(16+c) mod 4⟩`, and for a row `r : Fin 1024`
   (bits `r_i`), `β_j(r) := ∑_{i<j} w i * alpha ch i + ∑_{i>j} w i * (r_i : K)`:
   `pureRound_maskOnly (c : Fin 10) (u : Fin 1024 → K) (j : Fin 10) :
   PayloadSplit.rounds ch j (fun a => τ_c * maskLinear 0 a ^ e_c * ∑ r, eq(a, r) * u r) =
   ∑ r, u r • (τ_c * eqPrefix(alpha ch, r, j)) • ((if r_j then X else 1 − X) * (C (w j) * X + C (β_j r)) ^ e_c)`
   where `eqPrefix(α, r, j) = ∏_{i<j} (if r_i then α_i else 1 − α_i)` and
   `eq(a, r)` is the Boolean selector `honestClaims`/`eqwB` uses. Route:
   `rounds_eval_of_vdeg` (degree ≤ e_c + 1 ≤ 22) and the Boolean tail sum
   collapsing to the single tail equal to `r`'s high bits; then polynomial
   extensionality on 28 nodes (`nodes_injOn`). State and prove the same for
   G (`pureRound_G`: factor `1 + maskLinear 16 a ^ 26`, `w' j := 275 + 150*j`)
   and for the Libra cells of D (`pureRound_libra (d : Fin 56)`: Z4c's table —
   mask total `512·(2 if d=0 else 1)`; round j<m constant `2^(8−j)·(2 if d=0 else 1)`;
   round j=m `2^(9−j)·X^d`; round j>m constant `2^(9−j)·α_m^d`, m = 8 for
   d < 28 and 9 otherwise). Connect each to the honest view: the round-j
   coordinates of `L π B ch (pureTrace B m)` for the tape `m` supported on
   that lane equal the corresponding closed form applied to the lane's
   balanced word (`maskOnlyColumns`/`dWord` apply `balance 0`; `h1Padding` is
   not a mask lane; state the lemmas for the word after balance).
3. **Silence in per-lane terms.** `mem_silentMasks_iff`: `nonRound (A (m,0)) = 0`
   iff for every lane the four claim rows, the two OOD values and the opened
   symbols at the queried fibres of that lane's word vanish and the
   `.inactiveSum`, `.openingCoeff`, `.finalCoeff` coordinates vanish — stated
   through the existing `linearPayload` cases, no new definitions.
   Final target: the new module; `#print axioms` for the three closed forms
   and `silent_mem_chain0`; standard caps and stop list.

**T2b-2b (route, not yet a statement).** On `Good`, `Chain0 ch ⊆
roundProjection (silent image)`: per round, the polynomials
`(X or 1−X)·(w_j X + β)^{e}` over the available β (the tails) and e (ten
exponents) together with G's degree-27 term and the Libra monomials span the
degree-≤27 space, Vandermonde-style in β, with the leading coefficients
nonzero because `w j ≠ 0` in characteristic 2³¹ − 1 and `α_j ∉ {0,1}`; the
silence constraints are then satisfied by solving inside each lane's kernel
(912-dimensional per M31 lane). Whether the argument is per round or global
is decided from the closed forms; a numeric probe of the per-round
triangular structure may precede the statement.

### Lead decision T2b-1′ (2026-10-13) — Lemma B retyped; the worker's stop is accepted

The T2b-1 worker stopped under the fixed-statement rule: `rounds_initial` as
written in the T2b-1 spec is ill-typed. `rounds ch j` is a linear map on
`PayloadSplit.PointFunction K = (Fin 10 → K) → K` (PayloadSplit.lean:15, 31),
and `VDeg 10 (fun _ => 27) f` is stated for the same `f`, whereas
`bsumB 10 : ((Fin 10 → Bool) → K) → K` (Zerocheck.lean:32). The stop is
correct and the statement is amended as follows; nothing else in T2b-1 moves.

**T2b-1′.1 (Lemma B, typed form).** For `f : PayloadSplit.PointFunction K`
with `VDeg 10 (fun _ => 27) f`:

```
rounds_initial : (rounds ch 0 f).eval 0 + (rounds ch 0 f).eval 1
               = bsumB 10 (fun b => f (ofBool b))
rounds_chain (j : Fin 9) :
  (rounds ch j.succ f).eval 0 + (rounds ch j.succ f).eval 1
               = (rounds ch j.castSucc f).eval (alpha ch j.castSucc)
```

`ofBool` is `R0P`'s `Zerocheck.ofBool` (Zerocheck.lean:22), the same map at
which Lemma A is already stated, so the two lemmas compose without change.
The right-hand side of `rounds_initial` is `bsum 10 f` by `bsum_eq_bsumB`
(Zerocheck.lean:36); the worker may prove either side first but the statement
is the `bsumB` form above.

**T2b-1′.2 (item 4, same composition).** The initial sums of `g`'s two
`originalRounds` read `η · bsumB 10 (fun b => fOrig … (actual … (0,n)) (ofBool b))`
and `η · bsumB 10 (fun b => fOrig … (actual … 0) (ofBool b))`; Lemma A gives
equality termwise at every `ofBool b`, which is what item 4 needs.

**Route note (not binding).** `rounds_eval_of_vdeg` turns each side of
`rounds_initial` into `∑ tail : Fin 9 → Bool, f (roundPoint ch 0 z tail)` for
`z = 0, 1`; `roundPoint ch 0 z tail = Fin.cons z (ofBool tail)` up to the
`Fin 9` re-indexing in HonestView.lean:169–172; `bsumB`'s recursion peels the
leading coordinate (`bsumB 10 g = bsumB 9 (g ∘ Fin.cons false) + bsumB 9
(g ∘ Fin.cons true)`), and `bsumB 9 h = ∑ b, h b` is the private
`lane_bsumB_eq_sum` in LaneMap.lean:915 — restate it in `R0Z/Chain.lean`
rather than widen its visibility in R0P. For `rounds_chain` the same peel at
coordinate `j+1` after the first `j+1` coordinates are fixed at `alpha`.

Everything else in T2b-1 stands as specified: Lemma A, `Chain0`,
`sRem_mem_chain0 (hgood : alpha ch 9 ≠ 1/2)`, the file split
(`R0Z/TerminalEligible.lean`, `R0Z/Chain.lean`), the hard rules, host attempts
from 3377 (one module at a time, `run2.sh` run directly), `#print axioms` for
the four results, evidence under `t2b1/`. The branch
`codex/t2b1-chain-20261012` created at 29314d487 continues; it rebases onto
this head before its first commit. Research under the current verdict
(PLAN, 2026-10-11): v7 stands.

### Lead decision T2b-1″ (2026-10-13) — item 4 corrected: H1 padding is a zero-sum shift (Lemma C); the second stop is accepted

The T2b-1 worker stopped a second time, correctly. Item 4 (and T2b-1′.2)
asserted that `fOrig … (actual … (0,n)) (ofBool b)` and `fOrig … (actual … 0)
(ofBool b)` agree termwise by Lemma A. They do not: `N K F = ExtTape F ×
EligibleNoise K F` (Partition.lean:17), `aff (0,n)` places `n.1` in extension
slot 1 (Partition.lean:22), and `applyAff` adds `h1Padding B (Sum.elim 0 tape)`
to lane 26 (MaskLayout.lean:109–117). Lemma A covers `applyEligible` only.
The worker's counterexample stands: with `n.2 = 0`, `n.1` supported at
(row 15, limb 0) with value 1, `μ = η = 1`, row 15 is copy-inactive
(`copyActiveRowMasks 0 = 6144`, bits 11 and 12 only; CopyConstants.lean:31),
the Copy residual there is the prescribed zero (`copy_inactive_residuals`,
Copy.lean:618), and the terminal moves by `μ·1 + μ²·(1−0)·1 = 2`.

**T2b-1″.1 (η).** `fOrig` already carries `η = ch.sem 14` (Shift.lean:367).
The initial sums in item 4 and T2b-1′.2 are `bsumB 10 (fun b => fOrig … (ofBool b))`
with no further factor.

**T2b-1″.2 (Lemma C — the H1 padding shifts terminal rows by a zero-sum amount).**
Three statements, in `R0Z/TerminalEligible.lean` (or `R0Z/Chain.lean`):

```
terminal_applyAff (pub : Public K) (B : PackBasis F) (u : Trace K) (tape : AffTape K F)
    (ch : Challenges K) (b : Fin 10 → Bool) :
  terminalValue pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B
      (honestClaims (applyAff B u tape) (ofBool b)) (ofBool b)
    = terminalValue pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B
        (honestClaims u (ofBool b)) (ofBool b)
      + (ch.sem 13 + ch.sem 13 ^ 2) * h1Padding B (Sum.elim 0 tape) (rowOf b)

h1Padding_sum (B : PackBasis F) (tape : MaskTape K F) :
  ∑ r : Fin 1024, h1Padding B tape r = 0

h1Padding_bsumB (B : PackBasis F) (tape : MaskTape K F) :
  bsumB 10 (fun b => h1Padding B tape (rowOf b)) = 0
```

Route for `terminal_applyAff`: `honestClaims_ofBool` (SemHonest.lean:158);
`applyAff` keeps columns 0..15 at every row and sets lane 26 to
`u 26 r + h1Padding B (Sum.elim 0 tape) r`; `terminalValue` reads only the
column-0..15 openings (`Fin.castLE`) and `y 0 26` (SemDecision.lean:74–80);
`laneAt` reads `h1` only in lane 28 (SemDecision.lean:45–49). Split on
`CopyActiveRow (rowOf b)`. Active: `h1Padding` is zero there by definition
(zero on `CopyActiveRow` rows; the dependent row 0 is inactive since
`Nat.testBit 6144 0 = false`, a tiny `decide`), so both claim vectors agree on
everything read. Inactive: `copy_inactive_residuals` makes lane 28 equal to 0
on both sides, `activeAt_ofBool` (SemHonest.lean:193) with the inactive
selector gives `activeAt = 0`, and the two explicit helper terms contribute
`μ·p + μ²·(1 − 0)·p`. Route for `h1Padding_sum`: split off `r = 0`; `balance 0`
writes minus the sum over `copyInactiveRows.erase 0` of the padded word; the
sum over `r ≠ 0` of `if CopyActiveRow r then 0 else extensionRaw B tape 1 r`
is the same sum (`Finset.sum_filter`; `copyInactiveRows` stays `irreducible`
as in HonestView.lean:18 — never enumerated). `h1Padding_bsumB` is
`bsumB_rowOf` (LaneMap.lean:933, public) applied to `h1Padding_sum`.

**T2b-1″.3 (item 4, corrected route).** Write `u_e := prepare pub
(applyEligible (h.build w) n.2) ch` and `u_0 := prepare pub (applyEligible
(h.build w) 0) ch`, so `actual … (0,n) = applyAff B u_e (aff (0,n))` and
`actual … 0 = applyAff B u_0 0` (PayloadSplit.lean:70–72; `aff 0 = 0`). At
every Boolean `b`, `terminal_applyAff` gives
`fOrig … (actual … (0,n)) (ofBool b) = η·(T(u_e, b) + (μ+μ²)·h1Padding B (Sum.elim 0 (aff (0,n))) (rowOf b))`
and `fOrig … (actual … 0) (ofBool b) = η·T(u_0, b)` (the zero tape pads by
zero: `extensionRaw` of 0 is 0 and `balance 0` of the zero word is 0).
Lemma A twice: `T(u_e, b) = T(prepare pub (h.build w) ch, b) = T(u_0, b)`.
So the termwise difference is `η·(μ+μ²)·h1Padding … (rowOf b)`, and its Boolean
sum is 0 by `h1Padding_bsumB` with `bsumB_add`/`bsumB_smul`
(Zerocheck.lean:59–72). With `rounds_initial` applied to both `fOrig`s
(`vdeg_fOrig`), `g`'s round-0 polynomial sums to 0 on {0,1}. The chain,
terminal and `nonRound` parts of item 4 are unchanged.

**T2b-1″.4 (`applyAff_zero` withdrawn).** `applyAff B u 0 = u` is false:
lanes 16–25, 27 and 28 are rewritten from the zero tape. Its terminal-level
role is `terminal_applyAff` at `tape = 0`, which is the form item 4 uses.
`#print axioms` is additionally required for `terminal_applyAff` and
`h1Padding_bsumB`. Everything else in T2b-1 and T2b-1′ stands. Research under
the current verdict (PLAN, 2026-10-11): v7 stands.

### T2b-1 completed — remainder in the chain space (2026-10-13)

Implemented T2b-1 with the T2b-1′ and T2b-1″ corrections on
`codex/t2b1-chain-20261012`, rebased before the first commit onto
`6853b7827a6e6f330bf2ed11e6a64532d73b9387`. The two accepted stops remain
recorded above and in `t2b1/evidence.json.previous_stops`. The only new
source modules are `R0Z/TerminalEligible.lean` and `R0Z/Chain.lean`;
`D12.lean`, `Shift.lean` and all R0P/R0/R0FS/R0C files are untouched.

**Lemma A and the family audit.** Namespace `R0Z.TerminalEligible` proves
`terminal_row_eligible` in the specified prepared-trace form. Its stronger
intermediate `terminal_eligible` applies to any trace, and
`prepare_eligible` uses `HelperInvariant.helper_eligible` to commute
preparation with eligible masking. `honestClaims_ofBool` and `selAt_ofBool`
reduce the terminal to its literal Boolean-row reads.

- Schedule uses the existing `schedule_initial_row` and
  `schedule_absorption_row`: selected cells are below row 912, at local
  row 0 or 12. Digest's entire key catalogue likewise reads below 912
  at local rows at most 12, including the symbolic frontier/carry cases.
- Path constructs the `forestPathUsed` witness from its six blocks and
  four base rows per block, protecting current columns 0–8 and all
  successor columns. Value supplies the translated `pairAuxUsed` witness
  for its three records, columns 0–10 at current/successor/xor12 rows.
  Conservation protects columns 0–2 at row 1014 and 0–1 at row 1015.
  Occupancy protects columns 0–10 at 1017 and 0–9 at 1018; its column-10
  term at 1018 has zero selector. Asset protects its four selected reads.
- Copy's endpoint accumulator, including its LogUp compression and all
  positivity links, is invariant by `HelperInvariant.protected_registry`.
  A generic list-fold congruence composes the endpoint facts without
  unfolding the registry or relying on private R0P lemmas. The terminal
  has one `copyFamily` lane for these reads, not separate LogUp/positivity
  terminal lanes.
- Poseidon uses the block selector and the local leading/full/internal
  weights. Current/successor reads at local rows 0–10 are protected;
  xor12 is used only at local row 0 and reads local row 12. At local rows
  at least 11 every branch weight is zero. No recurrence or permutation
  is evaluated. Every effective C1 read excludes row 1023.

**Lemma C.** In the same module, `terminal_applyAff` has exactly the
T2b-1″ correction `(μ + μ²) * h1Padding B (Sum.elim 0 tape) (rowOf b)`.
On active rows the padding is zero (row 0 is inactive); on inactive rows
`copy_inactive_residuals` removes the H1-dependent lane. `h1Padding_sum`
applies generic finite-set balancing to the literal inactive support;
`mem_inactive` unfolds only filter membership, never its universe.
`h1Padding_bsumB` follows from the public `bsumB_rowOf`. The false
`applyAff_zero` trace identity is not asserted.

**Lemma B and the chain space.** Namespace `R0Z.Chain` proves
`rounds_initial` with `bsumB 10 (fun b => f (ofBool b))`, and `rounds_chain`
with the specified `j.succ`/`j.castSucc` indices. Both use
`rounds_eval_of_vdeg`, symbolic Boolean sums and `Fin.cons` tail
re-indexing. `roundPoly j` generalizes `round9Poly` (their equality at
j = 9 is definitional). `Chain0 ch : Submodule K (Payload K)` is the
intersection of K-linear kernels; `mem_chain0_iff` exposes exactly the
nonround-zero, initial-zero, nine boundary, and terminal-zero conditions.
`nonRoundK_apply` identifies the K-linear projection with D12's existing
F-linear projection on every payload.

`original_bsum_actual` combines A and C for each tape: `fOrig` carries eta
once, and the H1 correction has zero Boolean sum. Thus `g` satisfies the
initial and boundary conditions by B. `dir` satisfies those same conditions
with round-9 polynomial `X - C (1/2)`; subtracting its scalar multiple
preserves them. The terminal condition is `Phi0_sRem`, since `claimMask`
vanishes on the round-only remainder. The final theorem is
`sRem_mem_chain0 (hgood : alpha ch 9 ≠ 1/2) : sRem h B x w ch n ∈ Chain0 ch`.
It needs no witness-validity premise and no stronger `Good` assumption.

**Replay evidence.** All 103 unchanged R0Z/R0P worktree sources were
SHA-256 checked against the staged host sources before attempt 3377.
The prescribed pinned workspace and cache on `dombarker@100.108.41.90`
were reused. Attempts 3377–3394 ran one module at a time with
`sh run2.sh N Module 7000 7` directly; the launcher took its own lock.
Each scope had MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0, TasksMax 128,
and timeout 900 s. Observed reservation: 24 GiB populated + 7 GiB,
below the 55 GiB safe limit. No cap was raised. Lean v4.32.0; Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`.

There were 18 focused attempts: four successful stages (C at 3379,
final TerminalEligible at 3385, B at 3390, final Chain at 3394) and
14 elaboration failures, all retained with hashes, diagnostics and repairs
in [t2b1/evidence.json](t2b1/evidence.json). No resource failure occurred.
Final `R0Z/TerminalEligible`: exit 0, 7.55 s, peak RSS 6,933,404 KiB.
Final `R0Z/Chain`: exit 0, 4.67 s, peak RSS 6,887,404 KiB. Maximum wall time
and RSS across all attempts were 7.55 s and 6,933,404 KiB; swaps were 0
throughout. The JSON records the base revision, each staged target SHA-256,
commands, receipts, and final source Git blob identities. No unchanged
full regression was repeated.

All six required `#print axioms` results are exactly
`[propext, Classical.choice, Quot.sound]`: `terminal_row_eligible`,
`terminal_applyAff`, `h1Padding_bsumB`, `rounds_initial`, `rounds_chain`,
and `sRem_mem_chain0`. Source scan: no prohibited proof escape or resource
option; `decide` only for the permitted bit-zero check and `0 ≠ 9` in
`Fin 10`. Explicit `Finset.univ` occurs only over the abstract index type
of the generic balancing lemma; no row, state or field universe is
computed. No binaries, no co-author trailer, no push.

This closes T2b-1's chain-membership obligation only. Nothing proves,
assumes or weakens `MaskImageOn Good`; the spanning/image obligations
remain research work. The deployment verdict is unchanged: v7 stands.

### Lead acceptance of T2b-1 (2026-10-13) — the remainder lies in the chain space; T2b-2a released

T2b-1 (`3058917af` on `codex/t2b1-chain-20261012`, one commit on
`6853b7827`) is accepted and cherry-picked onto `v8-reference`. Reviewed
against the evidence:

- **Statements.** `terminal_row_eligible` (Lemma A), `rounds_initial` and
  `rounds_chain` (Lemma B in the T2b-1′ typed form), `terminal_applyAff`,
  `h1Padding_sum`, `h1Padding_bsumB` (Lemma C of T2b-1″), `roundPoly j`
  (with `roundPoly_nine : roundPoly 9 = round9Poly` by `rfl`),
  `Chain0 ch : Submodule K (Payload K)` as the meet of four K-linear kernels
  with `mem_chain0_iff` exposing exactly the four D17.3 conditions, and
  `sRem_mem_chain0 … (hgood : alpha ch 9 ≠ 1/2) : sRem h B x w ch n ∈ Chain0 ch`
  — every statement is as fixed in the LOG. No premise was added; no
  `Good` clause beyond `alpha ch 9 ≠ 1/2`; nothing touches `MaskImageOn`.
- **Proof substance (lead inspection).** Lemma A is the per-family audit:
  Schedule and Digest read below row 912 at local rows ≤ 12; Path and Value
  construct the `forestPathUsed`/`pairAuxUsed` witnesses; Conservation,
  Occupancy and Asset protect their fixed cells; Copy (one terminal lane,
  including LogUp compression and positivity links) is invariant by
  `protected_registry` through a generic list-fold congruence; Poseidon by
  the FINDINGS-Z6 rule (current/successor reads at local rows 0–10, xor12
  only at local row 0 reading local row 12, every weight zero at local rows
  ≥ 11, blocks ≥ 57 selected off) — no permutation or recurrence evaluated.
  `prepare_eligible` commutes preparation with eligible masking via
  `helper_eligible`. Lemma C splits on `CopyActiveRow (rowOf b)` exactly as
  specified (`zero_inactive` from `copyActiveRowMasks 0 = 6144`,
  `copy_inactive_residuals` on inactive rows); `h1Padding_sum` is a generic
  finite-set balancing lemma applied with `copyInactiveRows` irreducible.
  `original_bsum_actual` is stronger than the item 4 route: for every tape
  `r : T K F`, `bsumB 10 (fOrig … (actual … r) ∘ ofBool) = bsumB 10 (fOrig …
  (prepare pub t ch) ∘ ofBool)`; the two instances `(0,n)` and `0` give `g`'s
  zero initial sum, Lemma B gives its chain, `dir` lies in `InitialChain0`
  (`two_ne_zero` from `nodes_injOn`), and the terminal condition is
  `Phi0_sRem` with `claimMask` vanishing on the round-only remainder.
- **Hard rules.** No `sorry`/`axiom`/`native_decide`/`admit`/`maxRecDepth`/
  `maxHeartbeats`; `decide` only on `Nat.testBit 6144 0` and `(0 : Fin 10) ≠ 9`;
  `fin_cases` only over `Fin 3`; `Finset.univ` only over the abstract index
  of the balancing lemma. Only the two new modules, the LOG section and
  `t2b1/evidence.json` changed; D12, Shift, R0P/R0/R0FS/R0C untouched.
- **Replay evidence (verified on the host).** Attempts 3377–3394, one module
  at a time, `run2.sh` run directly, caps 5G/7G/swap 0/900 s, no cap raised;
  103 unchanged modules hash-checked before 3377. Final `R0Z/TerminalEligible`
  attempt 3385: exit 0, 7.55 s, peak RSS 6,933,404 KiB, swaps 0; final
  `R0Z/Chain` attempt 3394: exit 0, 4.67 s, peak RSS 6,887,404 KiB, swaps 0.
  `evidence/sha-3385.txt` and `sha-3394.txt` match the committed sources
  (`236743…df805`, `c0e5ce…a4e8`) and the staged host copies. Both
  `out-N.log` files carry the six `#print axioms` lines, each exactly
  `[propext, Classical.choice, Quot.sound]`. Host attempt counter: next 3395.

**Decision D19.** D17.3 clause (i′) is now split: `sRem … ∈ Chain0 ch` is
proved for every `n` with `alpha ch 9 ≠ 1/2` (T2b-1). What remains of (i′)
is `Chain0 ch ⊆ range (A ∘ inlM)` on `Good` (T2b-2a: `silent_mem_chain0`,
the closed forms; T2b-2b: spanning), and (ii′) `cTilde w − cTilde w' ∈ range A`.
T2b-2a is released as specified in "User direction (2026-10-12)", base this
commit, attempts from 3395. Research under the current verdict (PLAN,
2026-10-11): v7 stands.

### Lead decision T2b-2a′ (2026-10-13) — item 3 corrected: silence includes the mask sum; the stop is accepted

The T2b-2a worker stopped under the fixed-statement rule: item 3
(`mem_silentMasks_iff`) is false as written. `nonRound` (D12.lean:80) zeroes
only the `.semanticCoeff` coordinates and retains `.maskSum`; the right-hand
side I listed omitted that coordinate. The worker's counterexample stands:
`π = Equiv.refl`, all field challenges zero, both circle points `(1,0)`,
`queries = ∅`, tape supported on mask-only lane 0 with word `δ₅₁₃ − δ₅₁₅`
(both rows inactive, so `balance 0` leaves it unchanged); every listed
condition holds, yet the mask sum is `(w₀+w₉) − (w₀+w₈+w₉) = −w₈ = −179 ≠ 0`
and the round-0 polynomial is `−179·X`. The stop is correct.

**T2b-2a′.1 (item 3, corrected statement).** Writing `v := (A h.transport B ch).comp inlM m`:

```
mem_silentMasks_iff (m : M K F) :
  m ∈ silentMasks h.transport B ch ↔
    v .maskSum = 0 ∧
    (∀ j c, v (.pointClaim j c) = 0) ∧ (∀ c, v (.extraClaim c) = 0) ∧
    (∀ j c, v (.ood j c) = 0) ∧ v .inactiveSum = 0 ∧
    (∀ i, v (.openingCoeff i) = 0) ∧ (∀ i, v (.finalCoeff i) = 0) ∧
    (∀ q s c, v (.opened q s c) = 0)
```

Each coordinate unfolds through `L` (PayloadSplit.lean:47–52): `.maskSum` is
`∑ bits : Fin 10 → Bool, maskLinear π B (ofBool bits) (pureTrace B m)` and the
others are the `linearPayload` cases (`claimsLinear`, `extraLinear`,
`oodLinear ∘ coeffsLinear`, the inactive-sum dot, `openingCoeff`/`finalCoeff`
through `batchLinear`, and `opened` gated by `q ∈ ch.queries`). The lemma is
stated at the coordinate level as above; the per-lane reading in the original
item 3 is its unfolding, not a separate statement. No new definitions.

**T2b-2a′.2 (items 1 and 2 unchanged).** Item 1's route already uses the
`.maskSum` coordinate: silence gives `v .maskSum = 0`, which `rounds_initial`
identifies with `p₀(0) + p₀(1)`. This is consistent with the corrected item 3
(the mask sum is exactly the initial-sum coordinate) and nothing in items 1–2
moves. Research under the current verdict (PLAN, 2026-10-11): v7 stands.

### Lead decision D20 (2026-10-13) — spanning fails on `Good` over the base field; predicate refinement; probe Z7; ZF1-0 inventory

While T2b-2a runs, the T2b-2b statement was prepared from the closed forms of
"User direction (2026-10-12)" item 2. A dimension count shows that the
intended statement, `Chain0 ch ⊆ roundProjection (A (silentMasks))` for every
`Good ch`, is **false**, so the predicate must be refined before T2b-2b is
written. Nothing proved so far is affected: T2a's chain
`MaskImageOn P → HVZK_on P → ZK_FS (ε_fs + badMass P)` holds for every `P`,
and T2b-1/T2b-2a hold on `Good` as stated. What changes is the predicate on
which `MaskImageOn` will be proved and the ledger term attached to it.

**D20.1 (the obstruction).** Let `F` be the mask base field (the `PackBasis`
subfield; M31 in the source) and take `ch` with every `alpha ch i ∈ F \ {0,1}`
and `alpha ch 9 ≠ 1/2`, so `Good ch` holds. At round 7, the tower-limb-`u`
component (`towerBasis` index 2) of the silent image has `F`-dimension at most
24, while `Chain0`'s round-7 component is all of `K[X]_{≤27}` (its only
coupling is the one chain condition), whose `u`-component has dimension 28:

- mask-only lane `c` has an `F`-valued word and factor
  `τ_c · (maskLinear 0 a)^{e_c}` with `τ_c = towerBasis ((16+c) mod 4)`; the
  `u`-lanes are `c = 2` (`e = 5`) and `c = 6` (`e = 15`). The round-7 row
  polynomial is `eqPrefix(α, r_<7) · (r_7 ? X : 1−X) · (w_7 X + β_7(r))^{e_c}`
  with `β_7(r) = Σ_{i<7} w_i α_i + Σ_{i>7} w_i r_i`; with `α ∈ F^10` every
  coefficient is in `F`, there are four tails (bits 8, 9) and two values of
  `r_7`, so the lane's image is `τ_c · (F-span of ≤ 8 polynomials in
  F[X]_{≤ e_c+1})`: `u`-component ≤ 7 + 8 = 15 dimensions;
- `G`'s word is `K`-valued; its round-7 polynomials
  `(r_7 ? X : 1−X)(1 + (w'_7 X + β'_7(r))^26)` lie in `F[X]` for `α ∈ F^10`
  (four tails, two bits), so its image is `K ⊗_F (≤ 8-dimensional F-space)`:
  `u`-component ≤ 8;
- the Libra lane `D` contributes a constant at rounds `j < 8` (Z4c table):
  `u`-component ≤ 1; the H1 padding is not a mask lane (it lives in `N`).

Total ≤ 24 < 28. The same count at `α ∈ {0,1}^10` is what Z4c observed
(constructed ranks 1,022 and 1,038, supports at `(7,d,k)` with `k ∈ {2,3}`);
the point here is that `Good` does not exclude the base-field case, which has
mass `(|F|/|K|)^10` under a uniform α-row. The mechanism is that the
mask-only lanes acquire `K`-multiples only through the low-bit scalars
`Λ_j := span_F { eqPrefix(α, ℓ) : ℓ ∈ {0,1}^j } ⊇ span_F {1, α_0, …, α_{j−1}}`;
`G` and `D` carry `K`-valued words and need no such scalars. With
`w_i = 3 + 22 i` an arithmetic progression, the distinct tail sums at round
`j` number 512, 256, 128, 42, 26, 15, 8, 4, 2, 1 for `j = 0..9` (subset sums
of an arithmetic progression collide: e.g. `w_6 + w_9 = w_7 + w_8`). By the
leading-degree (divided-difference) argument, `G` alone spans all 28 degrees at
rounds 0–3, degrees 1–27 at round 4 (degree 0 from `D`'s constant), degrees
12–27 at round 5, 19–27 at round 6 and 23–27 at round 7; `D` spans rounds 8
and 9 entirely (`h8`, `h9` monomials). The mask-only lanes, under `Λ_j = K`,
span degrees 0–22 at every round by the same argument (lane `e` contributes
leading degrees `e−3 … e+1`; the ten exponents cover 0–22 without gaps). So
`Λ_5 = Λ_6 = Λ_7 = K` is sufficient, and the base-field case shows some such
condition is necessary.

**D20.2 (predicate, provisional).** The candidate refinement is
`Good₂ ch := Good ch ∧ span_F {1, alpha ch 0, …, alpha ch 4} = K`
(then `Λ_5 ⊆ Λ_6 ⊆ Λ_7` are all `K`). Its failure mass under a uniform α-row
is at most `(#3-dimensional F-subspaces containing 1) · (|F|^3/|K|)^5 =
(|F|^2+|F|+1)·|F|^15/|K|^5`. In the proved protocol the α-row is drawn in
`K = SemE = WideExact` (SemD3Glue.lean:528), where this is negligible; for a
QM31 instantiation it is ≈ 2^-93, and the sharper bound using the products
`α_i α_k ∈ Λ_5` would be needed to stay below 2^-100. The exact predicate is
fixed after Z7 reports; the T2b-2b statement is written then.

**Z7 (numeric probe; Claude agent; Rust; no Lean; no host Lean job).** Extend
`z4/probe.rs`'s Z4c machinery (`Ech`, `lane_eliminate`, `pure_c`, `full_c`,
`gate_c`, Z4c's D13 transport and challenge replay, `summarize`) into
`z4/z7.rs` + `run-z7.py`, keeping the base routines byte-for-byte. For each
α-structure below, report per round `j` the `F`-rank of the round-`j`
projection of (a) the constructed silent image and (b) the unconstrained pure
image, the total silent rank, and Z4c-style excess supports `(j,d,k)` against
`Chain0`-targets, on 5 challenge vectors per structure (all other challenges
as Z4c; `alpha 9 ≠ 1/2` and `α_i ∉ {0,1}` enforced):
 (A) α uniform in K (control; expect 112 per round, 1,076 total);
 (B) all `α_i ∈ F \ {0,1}` (expect the D20.1 deficiency at rounds 6–7, and
     the measured round-5 behaviour);
 (C) `α_0..α_4 ∈ W`, `W` a random 3-dimensional `F`-subspace containing 1,
     `α_5..α_9` uniform in K; (D) `α_0..α_5 ∈ W`; (E) `α_0..α_6 ∈ W`;
 (F) `α_0, α_1 ∈ span_F{1, α_0}` (2-dimensional), rest uniform;
 (G) `α_0..α_4` uniform, `α_5..α_9 ∈ F` (late coordinates only; expect no loss);
 (H) as (A) but with mask-only words restricted to rows with low bits
     `r_<j = 0` for the round-`j` matrix (diagnostic for the `Λ_j` mechanism).
Also print the distinct-tail-sum counts per round and, for (A), the
leading-degree pivot sets per lane at rounds 5–7. Optimised build under a
cgroup with explicit caps (`run-z7.py` in the style of `run.py`), source
manifest, receipts; findings as `z4/FINDINGS-Z7.txt` + `summary-Z7.json` +
`evidence-Z7.json` (the lead converts the findings to `.md`). No production
or Lean source changes. Stop rule: if (A) does not reproduce 1,076 on every
vector, stop and report.

**ZF1-0 (inventory and proposal; Claude agent; no proofs; no host).** Produce
`zf1/INVENTORY-ZF1.txt`: exact names, files and lines of every object ZF1
composes — `FsStatement` (`ROMView`, `FSExperiments`, `ZK_FS`, `ROMBridge`,
`ROMReduction`, `middleReal/Ideal`, `zkfs_of_hvzk_perfect`), `FsGood`
(`badMass`, `zkfs_of_hvzk_on`, `zkfs_of_maskImageOn_good`), `ZkStatement`
(`ModelSamplers`, `SamplerLaw`, `honestRows`, `honestView`,
`combinedSamplers`, `R0Obligations`, the 32-row schedule at line 449),
`FS2.Duplex` (`Params`, `samp`, `stateOf`, `absorbA/squeezeA/advanceA` and
their injectivity/disjointness lemmas, `Chal`), `FS2.Statement`
(`Sampler`, `toProgram`), `AspisV8R19.MemoizedProgramLaw` (`Program`, `eval`,
`lazyMean`, `Table`, `put`, `complete`), `AspisV8R19.AdaptiveFirstReadLaw`
(`FreshFrom`, `lazyMean_eq_independentMean`,
`complete_oracle_eq_independentMean`, `empty_oracle_eq_independentMean`,
`squeezeProgram_fresh_iff`, `independentMean_bind`), the decoders
(`R0C.V3.DQ.σQ`, `R0C.ModuloField.ordinary/gamma`, `ordinary_mass`,
`ordinary_mass_257`, `ordinary_event`), `R0P.SemDuplex.combinedOwn_law` and
`samp_mean`, and the field of the α-row (`SemE := WideExact`). Then a
proposal, as text with Lean signatures but no proofs: (1) the concrete
`FSExperiments` instance — adversary as a view-dependent oracle program with
its own coins, real experiment = the honest 31-round duplex program evaluated
on a uniform oracle function followed by the adversary's program, observer
log = its reads, ideal = the same with the simulator's instance; (2) the
`ROMBridge` — coins = the per-round absorb/squeeze/advance states, a fresh
table for the adversary's other reads and its coins; `draw` = the challenges
`σ_i` of the squeeze states in the 32-row schedule; `extend` = answering the
adversary's reads at prover addresses (recomputable from the view's messages)
from the recorded states, otherwise from the fresh table; (3) `ε_real`,
`ε_ideal` = the `FreshFrom`-failure mass (an adversary read hitting a prover
address before the prover does, or a prover address repeating), with the
bound shape in terms of the query count and `|State|` and the lemmas that
give it; (4) the `badMass Good` identification — per α-round mass of
`{0, 1}` (and `1/2` at round 23) under the semantic decoder through
`ordinary_mass`/`combinedOwn_law`, naming which `Params.σ` the semantic rounds
14–23 use in `R0Obligations` and what is data there. List every gap or
mismatch found. The lead fixes the ZF1 statements from this report.

### Lead decision D20′ (2026-10-13) — ZF1-0 accepted; α lives in the QM31 subfield; the probes' batching field does not match the proved protocol; composition theorem to be restated

ZF1-0 (`7aead2702` on `codex/zf1-inventory-20261013`, cherry-picked as
`0120ebd64`; `zf1/INVENTORY-ZF1.txt`) is accepted as an inventory. Its two
substantive findings were checked against the sources and both hold.

**D20′.1 (the α-row field; corrects D20.2).** The semantic challenges are
decoded by `semChal s = algebraMap QM31Exact WideExact (qm31Sample s)`
(SemD2.lean:206), fixed for rows 0–24 by `hσsem` in `combined_fiat_shamirZ`
(MaskFiatShamir.lean:124–125). So in the proved protocol `K = SemE =
WideExact` but every semantic challenge, including the α-row (rows 15–24,
`alpha ch i = ch.sem (15+i)`), lies in the QM31 subfield `K₄ ⊂ K`
(`[K : K₄] = 2`, `[K₄ : F] = 4` for `F` the M31 pack field). D20.2's
`span_F {1, α_0, …, α_4} = K` is therefore never satisfied and is withdrawn.
The corrected picture: the mask words are `F`-valued (mask-only lanes) or
`K₄`-valued (`pack4 B`: G, H1, D), the tower factors `τ_c ∈ K₄`, and with
`α ∈ K₄^10` every round polynomial of the mask image has coefficients in
`K₄`; `sRem` is `K₄`-valued too (all semantic challenges and trace values
are). The spanning target is therefore
`Chain0₄ ch := { v ∈ Chain0 ch : ∀ cell, v cell ∈ K₄ }`, an `F`-subspace of
dimension `4·269 = 1076` — Z4c's number — and the refined predicate is
`Good₂ ch := Good ch ∧ (∀ i, alpha ch i ∈ K₄) ∧ span_F {1, α_0, …, α_4} = K₄`
(with the `Λ_5 = K₄` variant including the products `α_0 α_i` if the density
must be sharper). Densities are over `K₄`, not `K`: the simple span condition
fails with mass ≤ `(|F|²+|F|+1)·|F|^15/|K₄|^5 ≈ 2^-93`; the product-refined
condition fails with mass `O(|F|^-4) ≈ 2^-124` (a 3-dimensional `F`-subspace
of `K₄` containing 1 is never a subalgebra, so each product condition costs a
factor `≈ 2/|F|`); the exact form is fixed in D21 after Z7. The α-law bound
is `semChal_event` (SemD2.lean:225): `|bad|·(1+δ_Q)/P^4` with
`δ_Q = P^4/256^32`; `badAlpha_density` (`21/|K|`) is the uniform-decoder
idealisation and is not the protocol's bound. D20's row numbering
("rounds 14–23") was the historical 31-row protocol's; the current 32-row
`combinedProtocolZ` has η at row 14 and α at rows 15–24.

**D20′.2 (batching field — a modelling gap in Z4b/Z4c/Z5 and Z7).** The
opening challenges are `ch.opening j`, rows 27–30, decoded by
`R0C.V3.DQ.σQ` (`gamma`/`ordinary`, ModuloField.lean:75–81) into
`WideExact`, and `linearPayload` weights the PCS coordinates with them:
`batchLinear π ch = ∑_c ch.opening 0 ^ c • …` (HonestView.lean:191),
`.openingCoeff` through `relationLinear (openingWeights π ch)` with
`ch.opening 1, 2`, `.finalCoeff` through `foldLinear (ch.opening 3)`, and
`.inactiveSum` with `ch.opening 0 ^ c`. These functionals are `K`-valued on
`K₄`-valued words: over `F` each is 8 conditions (2 over `K₄`). The Rust
probes set `gamma = 7 ∈ QM31` (probe.rs:2387, 2448, 2558, 2716) and cancel
the batched word with the D-lift `T_D = −γ^{c−28} t`, which is `K₄`-valued
and cannot cancel a `WideExact`-weighted combination; with `γ ∈ K ∖ K₄` a
zero batched word needs two `K₄`-valued lanes per row (G and D), which would
consume G's round contributions. So the Z4c/Z5 silent-rank gate (1,076) and
the (i′)/(ii′) passes certify a QM31-batching variant, not the proved
protocol's payload. This does not touch T2a, T2b-1 or T2b-2a (stated for any
`K`), but no spanning statement for the proved protocol is credible until the
gate is redone. **Z8 (numeric; after Z7 reports):** re-run the silent-rank
gate with `WideExact` batching challenges (aspis-core's `WideExact`
arithmetic; `K`-valued functionals eliminated over `F` as 8 coordinates),
with silence defined by the actual coordinates — `.openingCoeff` (7),
`.finalCoeff` (256), `.inactiveSum`, and per lane `.pointClaim`,
`.extraClaim`, `.ood`, `.opened` — not by the zero-batched-word proxy; report
the silent rank against 1,076 = `dim_F Chain0₄` and the (i′)/(ii′) passes on
5 vectors. **T2b-2b is HELD until Z7 and Z8 report**; D21 writes its
statement from both.

**D20′.3 (composition theorem; ZF1-0 gap G2).** `zkfs_of_hvzk_on` and
`zkfs_of_maskImageOn_good` (FsGood.lean:97–98, 120–121) require
`badMass P bridge adv x ≤ ε_bad` for **every** bridge; a constant-draw bridge
at a bad challenge has `badMass = 1`, so the hypothesis forces `ε_bad ≥ 1`
and the theorems are vacuous for the intended use. They are true but
superseded. **Job ZF-A (Lean; after T2b-2a lands; one job at a time):** in
`R0Z/FsStatement.lean` add

```
def ROMReductionWith (bridge : ROMBridge K CommitHandle Aux fs.Adversary)
    (x) (ε_real ε_ideal : ℚ) : Prop :=
  0 ≤ ε_real ∧ 0 ≤ ε_ideal ∧
  ∀ (hx : InLanguage h x) (adv : fs.Adversary) (w : h.Instance), h.public w = x.1 →
    |mean (realTest h B outputs fs adv x w) - mean (middleReal h B outputs fs bridge adv x w)| ≤ ε_real ∧
    |mean (middleIdeal h B outputs fs bridge adv x hx) - mean (idealTest h B outputs fs adv x hx)| ≤ ε_ideal
theorem romReduction_iff : ROMReduction h B outputs fs x ε ↔
  ∃ bridge ε_real ε_ideal, ROMReductionWith … bridge x ε_real ε_ideal ∧ ε_real + ε_ideal ≤ ε
```

and in `R0Z/FsGood.lean`

```
theorem zkfs_of_hvzk_on_bridge (P) (hh : HVZK_on P h B outputs x) (bridge) (ε_real ε_ideal ε_bad : ℚ)
    (hr : ROMReductionWith h B outputs fs bridge x ε_real ε_ideal)
    (hmass : ∀ adv, badMass P bridge adv x ≤ ε_bad) :
    ZK_FS h B outputs fs x (ε_real + ε_ideal + ε_bad)
theorem zkfs_of_maskImageOn_good_bridge : MaskImageOn Good h B x →
    ROMReductionWith … bridge x ε_real ε_ideal → (∀ adv, badMass Good bridge adv x ≤ ε_bad) →
    ZK_FS h B outputs fs x (ε_real + ε_ideal + ε_bad)
```

(the existing proofs transfer; `middle_means_close` is unchanged). The old
theorems stay with a docstring "superseded by the `_bridge` forms (D20′.3)".

**D20′.4 (ZF1 plan, from the inventory; statements fixed in D22).** The
target protocol is the 32-row `combinedProtocolZ` with the four σ
hypotheses of `combined_fiat_shamirZ` and `p.rounds = 32`
(`R0Obligations` is the historical Z1 object). The FS experiments are built
from `JointView.view`/`HonestView.run` and `ZkStatement.messages` (not from
Z1's `honestRows`); the adversary is a deterministic post-proof oracle program
`View → Program (Addr L) State Bool` (randomised adversaries follow by
averaging over their coins outside `ZK_FS`, which quantifies over all
adversaries — resolves G5). The bridge coins are the per-row absorb/squeeze/
advance states, the row-31 chain states and a fresh table for the adversary's
other reads; `draw` applies the row decoders to the squeeze coins; `extend`
recomputes the prover's addresses from the view's messages and answers from
the recorded states, else the fresh table. `ε_real = ε_ideal` is the mass of
a repeated prover address (110 reads: 31·3 + 1 + 16), bounded through
`lazyMean_eq_independentMean` on a collision-free variant plus an
identical-until-bad step (G10); `complete_oracle_eq_independentMean` is not
the right lemma because the adversary's re-reads break `FreshFrom` by design.
`badMass Good ≤ 21·(1+δ_Q)/P^4` by `semChal_event` and independence of the
bridge coins. Gaps to be closed inside ZF1: G3 (causality of `messages … i`
in the challenge rows `< i`), G6 (a ZK duplex `Params` over
`ZkStatement.Msg` with its own `enc`; statement binding and source bytes are
D7, outside), G7 (`toChallenges` projection), G8 (byte/`Fin 256`
conversions), G9 (`absorbA` injectivity), G10, G11 (`R0Z.mean` vs
`OracleResampling.mean`). Order after T2b-2a: ZF-A → (Z7, Z8 → D21 →
T2b-2b) → ZF1a (definitions, bridge, G3/G6/G7) → ZF1b (ε via freshness) →
ZF1c (badMass). Research under the current verdict (PLAN, 2026-10-11): v7
stands.

### Lead acceptance of Z7 (2026-10-13); decision D20″ — corrections to D20.1, the predicate fixed as `Good₂`, Z8 issued

Z7 (`8dfaa3a4c` on `codex/z7-alpha-structures-20261013`, cherry-picked;
`z4/z7.rs` as a module of `probe.rs` with a `--z7` dispatch, `run-z7.py`,
`FINDINGS-Z7.txt` (lead copy `FINDINGS-Z7.md`), `summary-Z7.json`,
`evidence-Z7.json`, `probe-Z7.log`, `z7-runs/`) is accepted. Reviewed: only
`z4/` changed; Z4c's rank and target routines are called unchanged; all 40
jobs replay Z4c's challenge lines byte-for-byte; structure (A) reproduces
silent rank 1,076 and the Z4c (i′)/derivative/(ii′) passes on 5/5 vectors;
host receipts (nuc, `MemoryHigh=3G`/`MemoryMax=4G`/swap 0): full scope
618.9 s, peak child RSS 75,200 KiB, swaps 0; 206 source hashes match.

**Results (identical on all 5 vectors per structure).** Silent per-round
`F`-ranks (max 108 at rounds 0 and 9 — the initial-sum and terminal conditions
each cut one `K`-dimension — and 112 elsewhere): (A), (C), (D), (E), (F), (G)
all attain the maximum at every round, total 1,076, excess 0. (B), all
`α_i ∈ F∖{0,1}`: round 7 drops to 93 (unconstrained 103), total 1,038; limbs
`(1, i, u, iu)` at round 7 are 24, 26, 21, 22 silent and 27, 28, 23, 25
unconstrained; Chain0 targets have excess 38, all at round 7; Z4c's (i′) and
derivative targets fail 5/5 with pivots `(7,14,2), (7,15,2), (7,16,2),
(7,16,3), (7,17,2)`; (ii′) passes. Rounds 5 and 6 do **not** lose rank under
(B). (H) (mask-only rows with low bits zero) loses only at round 7 in the
unconstrained projection (108); its silent drops at rounds 6–7 are an
artefact of too few rows for the 113 raw observations.

**D20″.1 (corrections to D20.1).** The `u`-limb count (≤ 24) is confirmed
(measured 23 unconstrained). Three details of D20.1 were wrong and are
replaced by the measured values: the distinct tail sums at rounds 0–2 are
130, 93, 64 (not 512, 256, 128; the counts 42, 26, 15, 8, 4, 2, 1 for rounds
3–9 stand); `G`'s unconstrained pivot coverage is degrees 0–27 at round 5,
12–27 at round 6 and 20–27 at round 7 (the leading-degree argument gives only
a lower bound on pivots; the actual span of `{q_B, X·q_B}` is `2·#tails`
dimensional); and consequently round 5 is spanned by `G` alone and round 6 by
`G` plus `F`-scalar lanes, so **only round 7 needs the `K₄`-scalar mechanism**.
The subspace structures (C)–(F) pass because `Λ_j` contains the products
`α_i α_k`, which leave any 3-dimensional subspace (none is a subalgebra); the
failing cases are those where all low-bit scalars stay inside a proper
subfield, of which (B) is the extreme.

**D20″.2 (predicate fixed).** With `K₄` the `F`-span of the pack basis
(the QM31 subfield for the tower basis), the predicate for `MaskImageOn` and
for the ledger is

```
Good₂ ch := Good ch ∧ (∀ i, alpha ch i ∈ K₄) ∧
            Submodule.span F {1, alpha ch 0, alpha ch 1, alpha ch 2, alpha ch 3, alpha ch 4, alpha ch 5} = K₄
```

It implies `Λ_6 = Λ_7 = K₄` (`Λ_7 ⊇ Λ_6 ⊇ span_F{1, α_0, …, α_5}` by summing
`eqPrefix` over the trailing bit), which is what the spanning proof needs at
rounds 6–7 (round 6 may not need it, per Z7; using it there is the safe
choice). Failure mass under independent `semChal`-distributed coordinates:
a proper `F`-subspace of `K₄` containing `1` and all six values has dimension
≤ 3; there are `|F|²+|F|+1` three-dimensional ones, and each coordinate lands
in a given one with mass ≤ `(1+δ_Q)/|F|`, so
`badMass(span) ≤ (|F|²+|F|+1)·((1+δ_Q)/|F|)^6 ≈ |F|^-4 ≈ 2^-124`, below the
2^-100 line; the `{0,1,½}` part is `21·(1+δ_Q)/P^4` (`semChal_event`); the
`∈ K₄` part has mass 0 under the decoder. The exact Lean form of `K₄` and of
the span condition is fixed in D21 with the T2b-2b statement, **after Z8**.

**Z8 (numeric; Claude agent, continuing Z7's branch and workspace).** The
gate must be redone for the proved protocol's payload (D20′.2): batching
challenges `ch.opening 0..3` uniform in `WideExact` (aspis-core's type; no
QM31 proxy), and silence defined by the actual `linearPayload` coordinates —
`.inactiveSum` (1 `WideExact` value), `.openingCoeff` (7), `.finalCoeff`
(256), computed with the R0 opening-layer functions (`batchLinear`: chord
quotient at `ch.circle 0/1` of each column's π-permuted natural-basis
coefficients, weighted by `γ^c`; the relation polynomial with
`openingWeights`; the fold by `ch.opening 3`), each `WideExact` value
eliminated over `F` as 8 coordinates — plus the per-lane `.pointClaim`,
`.extraClaim`, `.ood`, `.opened` as in Z4c. No zero-batched-word proxy and no
D-lift. Report, on 5 Z4c vectors: silent rank against 1,076 (= `dim_F
Chain0₄`), per-round ranks, (i′)/(ii′) passes with the targets' PCS
coordinates recomputed under `WideExact` batching, for structures (A) and (B),
plus (I) all `α_i` in the quadratic subfield `K₂ = F(i)` and (J) `α_0`
uniform in `K₄`, `α_1..α_6 ∈ F`, `α_7..α_9` uniform (both test `Λ_7` inside a
proper subfield or a 2-dimensional span). Stop rule: if the opening-layer
functionals cannot be evaluated column-wise from the existing Rust, stop and
report what is missing; if (A) under `WideExact` batching gives a silent rank
below 1,076, report the per-round and per-limb deficit and the excess
support — that is a finding, not an error. Same caps, receipts, manifest and
evidence format as Z7; `FINDINGS-Z8.txt`. T2b-2b stays held until Z8 lands.
Research under the current verdict (PLAN, 2026-10-11): v7 stands.

### Lead acceptance of Z8 (2026-10-13); decision D20‴ — the batching gap closes numerically; the hold on T2b-2b lifts into a proof-design job

Z8 (`c052a8f09` on `codex/z8-wide-batching-20261013`, cherry-picked; `z4/z8.rs`
as a `probe.rs` module with a `--z8` dispatch, `run-z8.py`, `FINDINGS-Z8.txt`
(lead copy `FINDINGS-Z8.md`), `summary-Z8.json`, `evidence-Z8.json`,
`probe-Z8.log`, `z8-runs/`) is accepted. Reviewed: only `z4/` changed; no
zero-batched-word proxy and no D-lift; silence is every non-semantic
`linearPayload` coordinate — per lane the Z4c set, and across lanes the 264
`WideExact` values `.inactiveSum` (1), `.openingCoeff` (7), `.finalCoeff`
(256), eliminated over M31 as 2,112 limbs; the opening layer is the R0 Rust
(`prover::quotient` column-wise, Lean's `totalWeights` from
`chord::quotient_weights`, `prover::round_polynomial`, `fold::fold_message`)
with a per-job check that the whole-column pipeline equals the sum of per-row
vectors on all 264 coordinates; `ch.opening 0..3` uniform in `WideExact`;
Z4c's 20 challenge lines and 25 terminal values replayed. Host receipts
(nuc, 3G/4G/swap 0): full scope 1,301.6 s, peak child RSS 145,732 KiB,
swaps 0; 207 source hashes match. One Rust/Lean mismatch was found and
handled inside the probe: `OpeningData::weights` omits Lean's `κ⁴ • libraWeight`
term; the probe adds it to match Lean. This is D14's fourth weight row, which
the Rust reference prover does not implement because R-H is held (D16); no
consequence under the current verdict, recorded for R-H.

**Results (identical on all 5 vectors per structure).**

| Structure | Silent | Initial retained | (i′) | (ii′) | Round-7 silent |
|---|---:|---:|---:|---:|---:|
| (A) α uniform | 1,076 | 1,080 | 25/25 | 25/25 | 112 |
| (B) all α ∈ F | 1,038 | 1,042 | 0/25 | 25/25 | 93 |
| (I) all α ∈ K₂ = F(i) | 1,068 | 1,072 | 0/25 | 25/25 | 108 |
| (J) α₀ ∈ K₄ generic, α₁..α₆ ∈ F | 1,076 | 1,080 | 25/25 | 25/25 | 112 |

Every other round is at its maximum (108 at rounds 0 and 9, 112 elsewhere)
in all four structures. (B)'s supports and pivots are Z7's exactly; (I)'s
Chain0 excess is 8 with pivots `(7, 24–27, {u, iu})`. In (ii′) the 2,112
batched limbs of the witness difference were matched exactly for every pair.

**D20‴.1 (what the numbers settle).** Under the proved protocol's
`WideExact` batching and its actual silence coordinates, the silent image is
the full `Chain0₄` (1,076) on generic challenges, and both clauses of
`MaskImageOn` hold numerically on Z4c's honest targets. The modelling gap of
D20′.2 is closed as a question of fact; what the Z4b/Z4c/Z5 gates certified
with the QM31 proxy, Z8 certifies for the real payload on the same vectors.
Rank is lost only when `Λ₇ = span_F{eqPrefix(α, ℓ)}` lies inside a proper
subfield of `K₄` (`F` in (B), `K₂` in (I)); (J) shows that a two-dimensional
`Λ₇ = span_F{1, α₀}` with `α₀ ∉ K₂` already suffices — the lane directions
`τ_c · Λ₇` then rotate across all four limbs.

**D20‴.2 (predicate).** `Good₂` as fixed in D20″.2 stands for the proof route
(it gives `Λ₆ = Λ₇ = K₄`, so lane spans are `K₄`-spans and the round argument
is `K₄`-linear), with one addition forced by `sRem`'s `K₄`-valuedness: all
semantic challenges, not only α, must lie in `K₄` (`λ, χ, θ, zc, μ, η` enter
the terminal), so

```
Good₂ ch := Good ch ∧ (∀ i : Fin 25, ch.sem i ∈ K₄) ∧
            Submodule.span F {1, alpha ch 0, …, alpha ch 5} = K₄
```

(mass 0 for the second clause under the decoder; ≈ 2^-124 for the third).
Recorded alternative, numerically sufficient by (J) and with a trivial density
proof (`((1+δ_Q)/|F|²)^7 ≈ 2^-434`): `Good₂′ := Good ∧ (∀ i, ch.sem i ∈ K₄) ∧
∃ i < 7, alpha ch i ∉ K₂`; it needs the direction-rotation argument instead
of `K₄`-linearity and is kept as the fallback if the design below prefers it.

**D20‴.3 (T2b-2b becomes a design job before a statement).** The hold is
lifted, but `Chain0₄ ⊆ A(silentMasks)` is a global rank statement about the
real silence kernel, and no Lean statement is fixed until its proof is
designed. **T2b-2b-D (design; Claude agent on Fable; no Lean, no host):**
write the complete mathematical argument for `Chain0₄ ch ⊆ (A h.transport B
ch ∘ inlM)(silentMasks …)` on `Good₂` with every nondegeneracy condition on
`ch.circle`/`ch.opening` made explicit, as a sequence of lemmas whose
statements transcribe to Lean, each tagged *structural* (provable for all
challenges, e.g. Vandermonde independence of evaluations at distinct points,
the `K₄`-linear leading-degree argument of D20.1/D20″) or *conditional*
(holds off an explicit bad set of challenges, with the set and its density
named). Decomposition to validate or replace: **(P) PCS cancellation** — the
264 batched coordinates and `D`'s own 112 observations are cancelled by `D`'s
round-free coefficients 56–1023 (968 `K₄`-coordinates) together with `G`'s
inactive-row sum (`D` alone reaches only the `K₄`-line `γ^28·K₄` of
`.inactiveSum`); **(Q) round spanning** — the round images of the mask-only
lanes' own-silence kernels (claims = MLE at the three α-points and the fourth
row, OOD = natural-basis evaluation at the circle points under π, opened =
codeword symbols at the 88 queried positions under π), of `G`'s own-silence
kernel with zero inactive-row sum, and of `D`'s Libra coefficients 0–55 span
`Chain0₄`; the design must state exactly which rank facts (Q) needs where the
row basis (claims, rounds) meets the coefficient basis (OOD, opened) through
the transport, and which of them are structural. Deliverable
`t2b2b/DESIGN-T2b-2b.txt`; the lead writes D21 (the Lean statement and the
T2b-2b job) from it. **Z8b (numeric; probe agent, same branch family):** on
Z8's (A) vectors check the decomposition — (1) the `F`-rank of the batched 264
coordinates plus `D`'s own 112 observations restricted to `D`'s coefficients
56–1023 (2,560 if full; 2,556 if `.inactiveSum` is short by the `K₄`-line),
and the same with `G`'s inactive-row sum added; (2) the `F`-rank of the round
image of {mask-only lanes ∩ own-silence} + {`G` ∩ own-silence ∩ zero
inactive-row sum} + {`D` coefficients 0–55} (expect 1,076); (3) the silent
rank of the subspace assembled from (1) and (2) (expect 1,076 — equality with
Z8's silent rank means the decomposition loses nothing). Any shortfall is a
finding that redirects the design. Research under the current verdict (PLAN,
2026-10-11): v7 stands.

### Lead acceptance of Z8b (2026-10-13); decision D20⁗ — the decomposition loses nothing globally, but its PCS block is not full rank; the design is redirected

Z8b (`166ed47cd` on `codex/z8b-decomposition-20261013`, cherry-picked;
`z4/z8b.rs` as a `probe.rs` module behind `--z8b`, `run-z8b.py`,
`FINDINGS-Z8b.txt` (lead copy `FINDINGS-Z8b.md`), `summary-Z8b.json`,
`evidence-Z8b.json`, `probe-Z8b.log`, `z8b-runs/`) is accepted. Only `z4/`
changed; Z8's WideExact batching and real silence coordinates; 5 (A) vectors,
identical numbers on each; host receipts (nuc, 3G/4G/swap 0): full scope
516.8 s, peak child RSS 217,884 KiB, swaps 0; 208 source hashes match.

**Correction of counts.** A `K₄`-valued lane (G, D) has 94 own observations
(3 point claims, 1 extra claim, 2 OOD, 88 opened, each `K₄`-valued) = 376
limbs, not 448; the "112" of an M31 lane is a limb count. Block (1) of
D20‴.3 therefore has 2,112 + 376 = 2,488 limb-functionals.

**Results.**
- Per-lane own-silence ranks on Z8's fibre set: mask-only lanes 16–25: 112
  each; G: 376 (380 with its inactive-row sum); D: 376; D restricted to
  coefficients 0–55: 224; to 56–1023: 372.
- **(1) PCS block on D's coefficients 56–1023:** rank 2,184 of 2,488; with
  G's inactive-row sum 2,188. Breakdown: batched 2,000 of 2,112 (2,004 with
  G); D-own 372 of 376; `.inactiveSum` 4 of 8 limbs (8 with G — the
  `K₄`-line effect predicted in D20‴.3); opening+final 1,996 of 2,104 (27
  `K₄`-functionals short). **The block is 300 limbs short of full rank**; the
  `.inactiveSum` line accounts for 4 of them.
- **(2) Round image of the (Q) generators** (mask-lane own-kernels, G's
  own-kernel with zero inactive-row sum, D's coefficients 0–55): 112 per
  round, 1,084 retained, 1,080 with initial zero (the terminal is not forced
  to zero because D's 0–55 are free there); Chain0 and (i′) targets already
  inside; the generators' silent part alone is only 988.
- **(3) Assembled** ((Q) generators + D's 56–1023): span 3,376 with 2,296
  silence pivots; initial-retained 1,080; **silent 1,076 = Z8's**; per round
  108, 112, …, 112, 108; Chain0 excess 0; (i′) 25/25; derivative 25/25.

**D20⁗.1 (what this means).** The modular picture "D's round-free
coefficients cancel the PCS coordinates; the lanes span the rounds" is false
as a lemma: D's high coefficients plus G's inactive sum cancel 2,188 of the
2,488 batched/own limbs, and the remaining 300 are cancelled by the surplus
of the other lanes' own-silence kernels (each mask-only lane has a
912-limb kernel of which only a bounded part carries round image). The
global statement stands — the assembled subspace is exactly the silent image
on these vectors — so the proof must be organised around a global
kernel-rank fact (the observation functionals restricted to the round-kernel
`ker R` have full rank, or an equivalent) or around a decomposition that uses
the lanes' surplus explicitly. The T2b-2b-D agent has been given these
numbers and asked to restructure accordingly, keeping the
STRUCTURAL/CONDITIONAL tagging and naming the numeric check that would
confirm each restructured lemma. D21 waits for the revised design. Research
under the current verdict (PLAN, 2026-10-11): v7 stands.

### Lead decision T2b-2a″ (2026-10-13) — item 2's Libra table restated in the local degree; the third stop is accepted

The T2b-2a worker stopped on item 2's Libra formula: the table in "User
direction (2026-10-12)" item 2 is written with `d : Fin 56` as both the
coefficient index and the exponent, but `libraWeight` (SemView.lean:65) is
`if j < 28 then alpha 8 ^ j else if j < 56 then alpha 9 ^ (j − 28) else 0`,
so for cells 28–55 the exponent is the local degree `d − 28`. The worker's
counterexample stands: `π = Equiv.refl`, D's limb 0 at row 28 equal to 1
(row 28 is copy-active, mask `6144` bit 12, so `balance 0` leaves the word
`δ₂₈` unchanged), `d = 28`, round 9: the actual polynomial is `1`
(`α₉^(28−28)`), the table said `X^28`; the actual mask total is `1024`, the
table said `512`. The stop is correct; Z4c's table used "degree `d` in `hm`"
in the local sense and I transcribed it as the coefficient index.

**T2b-2a″.1 (item 2, Libra, corrected).** For `d : Fin 56` let
`m := if d.val < 28 then 8 else 9` and `e := d.val % 28` (the local degree).
`pureRound_libra (d : Fin 56)`: for a tape supported on D's coefficient `d`
with balanced word value 1 there —

```
mask total        512 · (if e = 0 then 2 else 1)
round j < m       C (2^(8−j) · (if e = 0 then 2 else 1))        (a constant)
round j = m       C (2^(9−j)) * X^e
round j > m       C (2^(9−j) · (alpha ch m)^e)                   (a constant)
```

Everything else in item 2 (the mask-only and G closed forms, the connection
to `L π B ch (pureTrace B m)` after `balance 0`) and items 1 and 3 (as
corrected by T2b-2a′) are unchanged. Check: `d = 28` gives `e = 0`, `m = 9`,
mask total `1024`, round-9 polynomial `1`, matching the counterexample.
Research under the current verdict (PLAN, 2026-10-11): v7 stands.

### Cross-reference (2026-10-13): the R1 programme in the Rust PLAN; privacy merge

The Rust PLAN section "Lead review of the `codex/100bit-spend-path-20261013`
checkpoint (2026-10-13)" amends the P2 verdict (the ordinary two-transaction
case now measures 1.34M/1.37M CU with the Pool adapter; the rollover case
fails; headroom is 25–57K) and re-states the fit gate as G_R1. For this
track it adds: **Z9** — the Z8 gate on the R1 payload (two folds, 64 final
values, D18 π, γ ∈ WideExact, ρ ∈ QM31) with real coordinates and no proxy,
on the checkpoint's two γ limb sets and structures (A)/(B)/(I)/(J); the
T2b-2b design to be stated for a payload family covering R0 and R1; ZF1 for
the 33-row schedule; **ZF2** — an efficient simulator obligation (the
checkpoint's PRIVACY-RANK-PATH is right that `Classical.choose` is not an
algorithm; the public mask-map route is to be fixed as a lead decision after
T2b-2b). The checkpoint found the γ-in-QM31 gap of D20′.2 independently and
compensates with both K₄-valued pads, as D20′.2 requires; its probe reaches
silent rank 1,076 on the actual R1 payload. Nothing in T2a, T2b-1, T2b-2a or
the D20 series changes. Standing verdict: v7 stands; R1 is a live candidate
under G_R1.
### T2b-2a completed — pure-mask round forms and the easy inclusion (2026-10-13)

Implemented on `codex/t2b2a-purerounds-20261013`, rebased before the first
commit onto `5ff677bf36be5af137b29f9bf09c819bfb29073c`. The accepted stops and
corrections T2b-2a′ (retain the mask sum) and T2b-2a″ (Libra local degree)
are recorded above and in `t2b2a/evidence.json.previous_stops`. The only new
source is `R0Z/PureRounds.lean`. It imports `Shift` and `Chain`, plus
`Z4Maps` solely to use its existing `silentMasks` submodule. No existing
Lean module changed.

**Easy inclusion and silence.** `silent_mem_chain0` has exactly the specified
non-round-silence premise, with no `Good` premise. `A_pure` identifies the
payload with `L (pureTrace m)`; `L_maskSum` and `rounds_initial` give its zero
initial boundary, `rounds_chain` gives the nine internal boundaries, and
`Phi0_A` with the silent point/extra claims gives the zero terminal value.
`mem_silentMasks_iff` is T2b-2a′'s coordinate-level equivalence, including
`.maskSum` and all eight listed groups of retained coordinates. Its proof
only projects or reconstructs the existing non-round map.

**Closed forms.** The only new definitions are `w`, `β` and `eqPrefix`.
`w` is parameterized by the source family: `w_zero` gives `3+22j` and
`w_sixteen` gives `275+150j`. `selector_round_match` and
`selector_round_mismatch` prove that each row's equality selector leaves
exactly its matching Boolean tail. `linear_round_match` splits the weighted
linear form into `w_j X + β_j(r)`. `power_rounds` applies
`rounds_eval_of_vdeg`, collapses the tail sum symbolically, and identifies
the polynomial on the 28 distinct nodes using `nodes_injOn`.
`pureRound_maskOnly` and `pureRound_G` specialize this formula, including
G's added constant 1. The mask-only functional and polynomial degree is
at most `e_c+1`, and `maskOnly_degree` proves `e_c+1 ≤ 22`; G's bound is 27.

`pureRound_libra` uses coordinate 8 or 9 and local degree `d.val % 28`.
A generic tuple equivalence isolates one Boolean coordinate; symbolic cube
cardinality supplies the powers of two. `pureLibra_maskSum` proves the
`512*(if e=0 then 2 else 1)` total. No Boolean cube, row universe, field or
literal registry is enumerated.

**Connection to the honest view.** The word lemmas identify `pureTrace`'s
mask-only, G and D lanes with `maskOnlyColumns`, balanced packed G, and
`dWord`, respectively. Raw-support lemmas prove the required trace support
from the tape components, including zero G/D or mask-only components as
appropriate; support is not an unproved premise of the final bridges.
`L_pure_maskOnly_coeff`, `L_pure_G_coeff` and `L_pure_libra_coeff` identify
the actual `.semanticCoeff j i` coordinates with the closed forms. For
Libra the unit-coefficient condition is imposed on the transported word
**after** `balance 0`; `L_pure_libra_maskSum` connects its total as well.
H1 padding is never treated as a pure mask lane.

**Replay.** Before attempt 3395, all 105 unchanged R0Z/R0P modules matched
the staged host hashes, including `TerminalEligible` and `Chain`. All 13
attempts (3395–3407) ran one module at a time in the pinned host workspace,
with `sh run2.sh N R0Z/PureRounds 7000 7` run directly, never under an outer
flock. Caps: MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0, TasksMax 128,
timeout 900 s, Lean `-j1 -M7000 -DElab.async=false`. The reported populated
reservation was 24 GiB plus this job's 7 GiB, below the 55 GiB safe limit.
No cap changed. Lean v4.32.0 and the pinned cache were reused.

Nine attempts failed during elaboration; four stages passed. Repairs were
local projection/unfolding control, dependent-index normalization, or proof
syntax; no statement or premise was weakened. Final attempt 3407: exit 0,
9.40 s wall, peak RSS 7,080,048 KiB, swaps 0. Across all attempts the maximum
wall time was 16.97 s and maximum RSS was 7,080,048 KiB; every attempt had
zero swaps. [t2b2a/evidence.json](t2b2a/evidence.json) records source hashes,
commands, metrics, diagnostics, repairs and host receipt hashes. No unchanged
full regression was repeated.

All four required `#print axioms` results are exactly
`[propext, Classical.choice, Quot.sound]`: `silent_mem_chain0`,
`pureRound_maskOnly`, `pureRound_G`, `pureRound_libra`. The corrected silence
equivalence and all four final honest-view bridges were also audited with
exactly those axioms. No prohibited proof escape or resource option occurs;
the sole `decide` is `(28 : Fin 29) ≠ 27`; the sole explicit `Finset.univ`
is over `Fin 10` in the weighted linear-form degree lemma. No binaries,
co-author trailer or push.

This closes T2b-2a only. Nothing proves, assumes or weakens `MaskImageOn
Good`; no spanning or deployment claim follows. The deployment verdict is
unchanged: v7 stands.

### Lead acceptance of T2b-2a (2026-10-13); ZF-A released

T2b-2a (`700dd4b4a` on `codex/t2b2a-purerounds-20261013`, one commit on
`5ff677bf3`, cherry-picked as `1cdcbd22b`) is accepted. Reviewed against the
statements fixed in "User direction (2026-10-12)" items 1–3 with T2b-2a′
(mask-sum coordinate) and T2b-2a″ (Libra local degree):

- **Statements.** `silent_mem_chain0` with exactly the non-round-silence
  premise and no `Good`; `mem_silentMasks_iff` at coordinate level with
  `.maskSum` and the eight retained groups; `pureRound_maskOnly`
  (`τ_c = towerBasis ((16+c) mod 4)`, exponent `maskOnlyFactorExponent c`,
  `w 0 j = 3+22j`, `β`, `eqPrefix` in the source's MSB-first `rowBits`
  order, selector `selAt a r`); `pureRound_G` (`1 + maskLinear 16 ^ 26`,
  `w 16 j = 275+150j`); `pureRound_libra` with `k = 8/9` and `e = d % 28`
  for the point function `a ↦ a k ^ e`, plus `pureLibra_maskSum`
  (`512·(2 if e = 0 else 1)`); and the honest-view bridges
  `L_pure_maskOnly_coeff`, `L_pure_G_coeff`, `L_pure_libra_coeff`,
  `L_pure_libra_maskSum`, stated for the words after `balance 0`
  (`maskOnlyColumns`, balanced packed G, `dWord`), with the Libra unit
  condition imposed on the transported word after balancing. Only `w`, `β`,
  `eqPrefix` are new definitions. `Z4Maps` is imported only for `silentMasks`.
- **Proof substance (lead inspection).** `power_rounds` is the generic closed
  form: `rounds_eval_of_vdeg`, the symbolic tail collapse
  (`selector_round_match/mismatch`, `tail_sum_selector`), the split
  `w_j X + β_j(r)` (`linear_round_match`), and identification on the 28 nodes
  (`polynomial_ext28`, `nodes_injOn`); degrees `e_c + 1 ≤ 22`
  (`maskOnly_degree`) and 27 for G. The Libra form isolates one Boolean
  coordinate by a tuple equivalence with symbolic cube cardinalities. Support
  lemmas derive the trace support from the tape components rather than
  assuming it. H1 padding is never a pure mask lane.
- **Hard rules.** No `sorry`/`axiom`/`native_decide`/`admit`/`maxRecDepth`/
  `maxHeartbeats`; one `decide` on `(28 : Fin 29) ≠ 27`; the only explicit
  `Finset.univ` is over `Fin 10`; all row and cube sums symbolic. Only
  `R0Z/PureRounds.lean`, the LOG section and `t2b2a/evidence.json` changed.
- **Replay evidence (verified on the host).** Attempts 3395–3407, one module
  at a time, `run2.sh` run directly, caps 5G/7G/swap 0/900 s, no cap raised;
  105 unchanged modules hash-checked before 3395. Final attempt 3407: exit 0,
  9.40 s, peak RSS 7,080,048 KiB, swaps 0; `evidence/sha-3407.txt` and the
  staged copy match the committed source (`227c7f58…b704c4`); `out-3407.log`
  carries nine `#print axioms` lines, each exactly
  `[propext, Classical.choice, Quot.sound]`. Host counter: next 3408.

**State of D17.3 (i′).** Proved: `sRem ∈ Chain0` (T2b-1, `alpha ch 9 ≠ 1/2`)
and `A(silentMasks) ⊆ Chain0` (T2b-2a). Open: `Chain0₄ ⊆ A(silentMasks)` on
`Good₂` (T2b-2b; design in progress per D20⁗) and clause (ii′). The numeric
record (Z4c, Z5, Z7, Z8, Z8b) supports both on generic challenges for the
proved protocol's payload.

**ZF-A is released** as specified in D20′.3 (`ROMReductionWith`,
`romReduction_iff`, `zkfs_of_hvzk_on_bridge`, `zkfs_of_maskImageOn_good_bridge`),
base the commit carrying this section, attempts from 3408. Research under the
current verdict (PLAN, 2026-10-13): v7 stands; R1 is a live candidate under
G_R1.

### ZF-A completed — bridge exposed in FS composition (2026-10-13)

Branch `codex/zfa-bridge-composition-20261013`, base
`4edacd5bda84f7808a87a29a466f7ff8eb6e6e26` (carrying T2b-2a acceptance).
The four statements fixed in D20′.3 compile as given, with no added or
weakened premise. `FsStatement.lean` adds `ROMReductionWith` immediately
after `ROMReduction`, retaining the two nonnegative comparison bounds for
the specified bridge, and `romReduction_iff`, which recovers the original
existential packaging and sum bound. `FsGood.lean` adds
`zkfs_of_hvzk_on_bridge` and `zkfs_of_maskImageOn_good_bridge`: the bad-mass
hypothesis now concerns the same bridge supplied to `ROMReductionWith`, and
the conclusion has error `ε_real + ε_ideal + ε_bad`.

The existing triangle-inequality proof transfers with the bridge supplied
as an argument. `middle_means_close` is byte-identical to the base, as are
the existing theorem declarations and proofs. Both old FsGood theorems
remain with the docstring “superseded by the `_bridge` forms (D20′.3)”. No
concrete bridge, ROM comparison certificate, challenge law, or numerical
bad-mass bound is supplied by this composition result.

Host: `dombarker@100.108.41.90`, pinned workspace
`/home/dombarker/project-offloads/aspis-fs-generic-20261006`. All 106 base
R0Z/R0P modules matched the staged host sources before the first attempt.
The existing Lean v4.32.0 / Mathlib cache was reused. Each module ran once,
in this order, using `sh run2.sh N Module 7000 7` directly; the launcher took
its own lock. Caps were MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0,
TasksMax 128, timeout 900 s, Lean `-j1 -M7000 -DElab.async=false`. Both
launches admitted 24 GiB populated plus this job's 7 GiB below 55 GiB.

| Attempt | Final target | Exit | Wall time | Peak RSS (KiB) | Swaps |
|---|---|---|---|---|---|
| 3408 | `R0Z/FsStatement` | 0 | 3.17 s | 6,847,708 | 0 |
| 3409 | `R0Z/FsGood` | 0 | 3.46 s | 6,859,556 | 0 |

All four required `#print axioms` results are exactly
`[propext, Classical.choice, Quot.sound]`: `ROMReductionWith`,
`romReduction_iff`, `zkfs_of_hvzk_on_bridge`,
`zkfs_of_maskImageOn_good_bridge`. All eleven printed declarations across
the two modules have that same result. No failed Lean attempt, cap increase,
dependency rebuild or unchanged full regression. Next host attempt: 3410.
[zfa/evidence.json](zfa/evidence.json), in the T2b-1 format, records source
SHA-256 and Git blob identities, dependency identity, commands, metrics,
axioms, and host receipt paths and hashes.

Only the two prescribed Lean files, this LOG section and that evidence JSON
changed. Neither target contains `sorry`, an `axiom` declaration,
`native_decide`, `admit`, `maxRecDepth`, `maxHeartbeats` or `decide`. No new
enumeration or broad unfolding; no binaries, co-author trailer or push.
This closes ZF-A only. The research verdict is unchanged: v7 stands; R1
remains a live candidate under G_R1.

### Lead acceptance of ZF-A (2026-10-15)

ZF-A (`0782fa3a7`, fast-forwarded onto `v8-reference` with L1 and L2) is
accepted: `ROMReductionWith`, `romReduction_iff`, `zkfs_of_hvzk_on_bridge`,
`zkfs_of_maskImageOn_good_bridge` as fixed in D20′.3; the old theorems keep
their "superseded" docstrings. Host attempts 3408 (`R0Z/FsStatement`, exit 0,
SHA `e79a9ae2…`) and 3409 (`R0Z/FsGood`, exit 0, SHA `9d3ec489…`) verified
against the host receipts; all axiom lines exactly `[propext,
Classical.choice, Quot.sound]`; no cap raised. The vacuity found by ZF1-0
(gap G2) is closed: the bad-mass hypothesis now quantifies over adversaries
for one exhibited bridge. Open on this track: T2b-2b (design agent stopped by
a provider session limit before writing; relaunched 2026-10-15), (ii′), ZF1,
ZF2. Host counter: next 3426.

### Lead acceptance of the T2b-2b design as a proposal (2026-10-15); Z8c issued; D21 waits for Z8c

The T2b-2b-D design (`5bedc6303`, cherry-picked; `t2b2b/DESIGN-T2b-2b.txt`,
Opus agent) is accepted as the working proposal, not as fixed statements.
What it establishes and what it changes:

- **Reduction.** The spanning half splits into (Q′) round cover — every
  K₄-valued chain vector with terminal 0 is the round image of an own-silent
  tape — and (B) the batched opening coordinates on own-silent round-kernel
  tapes reach what they reach on all own-silent tapes. This replaces the
  refuted (P)/(Q) split (D20⁗). On own-silent tapes the observations satisfy
  exactly 24 K-relations (192 limbs) from existing R0 lemmas (`round_eval`,
  `round_boundary`, `fold_encoded` on the 22 fibres), matching Z8's 1,920.
- **Why Z8b's (P) block fell short.** On D's coefficients 56–1023 with zero
  OOD values the chord quotient is divisible by x^28, so its fold vanishes on
  fibres 0–13; G's 56 low rows supply them.
- **Model gap (correction F4).** In Lean every mask lane is balanced at row 0
  (`balance 0`), so each lane's word space is a hyperplane and the inactive sum
  vanishes identically. Z8/Z8b used unbalanced unit sources, a superset of the
  Lean mask space by up to 10 limbs. **1,076 is therefore an upper bound for
  the Lean model, not yet a measurement.** Z8c decides it.
- **Predicate.** The route needs Λ₄ = K₄, which Good₂ does not give. Proposed
  `Good₃ := Good ∧ (∀ i, ch.sem i ∈ K₄) ∧ (at least three of α₀..α₃ ∉ K₂)`,
  plus explicit nondegeneracy conditions on the circle points and fold
  challenge. K₄ as a subfield needs a premise PackBasis lacks (i² ∈ F,
  u² ∈ F + F·i; true for QM31). Total conditional mass excluding the open
  item ≈ 2^-104.3 (privacy ledger term; about 4 bits of margin), with the
  minor bounds valid only once nonvanishing witnesses exist.
- **Main risk (OT-open).** Transversality of the 88 opened symbols to each
  lane's round kernel has no proof route for all query sets. If none is found
  it enters the theorem as an explicit, numerically checked premise, labelled
  as such in the ledger.
- Clause (ii′) is not covered. The R1 payload changes every count.

Next: **Z8c** (probe, §3.3 of the design; Opus agent) on the balanced Lean
model; J1–J3 and J5a can be written independently of Z8c; D21 after Z8c; an
OT-open research item before J6. Verdict unchanged.

### Lead acceptance of Z8c (2026-10-15); D21: design corrections, Z8d issued, Lean statement still waits

Z8c (`6c93dfb64`, Opus agent; `z4/FINDINGS-Z8c.md`, `summary-Z8c.json`,
`evidence-Z8c.json`) is accepted. Receipts: 36 per-process records, exit 0,
swap 0, peak RSS 314 MB per job, cgroup peak 1.59 GB under MemoryMax 4G;
209 source hashes match; all 35 CHALLENGE lines and A's 25 terminal triples
match probe-C.log. Every number is identical across the 5 vectors of each
structure.

**D21.1 Model gap closed.** On the balanced Lean sources (`balance 0`, no
`.inactiveSum` proxy) the silent rank is 1,076 for A, J, K and M. Z8 and Z8c
agree on every per-round and per-limb rank; the only difference is the 8
`.inactiveSum` limbs, now identically 0. 1,076 is a measured rank of the Lean
model on these vectors, not only an upper bound (F4 resolved).

**D21.2 Verifier relations exact.** The annihilator of bat(ker own) has
dimension 200 and is spanned by `.inactiveSum` plus the 24 relations (S1, S2,
22 × S3_u), which are independent. F2 is confirmed; the (B) target is fixed as
"bat(ker own) = the common zero set of these 25 relations".

**D21.3 Predicate.** L (α₀..α₅ ∈ F) fails at the statement level: silent 994,
(ii′) 0/25, full conditioned image 1,073. Good₂′ at i = 6 alone is rejected.
K passes with Good₃ false, so Good₃ is sufficient, not necessary. Good₃ stays
the proof predicate: a sufficient predicate with a mass bound is all the
ledger needs, and weakening it buys at most a fraction of a bit.

**D21.4 OT_l correction.** On ker R_l the lane's own observations have rank 108
only for e ∈ {1, 3, 5} and 104 for every e ≥ 7, not "108 for e ≤ 13". Rel_l in
OT_l includes claim₂ for e ∈ {7, 9, 11} as well, using rounds beyond 6. The
round-6-only statement F5 holds exactly as the design predicted. OT′ holds as
designed (mask lanes 108, G 372, D 372).

**D21.5 The x^28 law is not confirmed and (B)'s split is not the f0..f13
split.** D-high misses 104 limbs (13 K-dims), not the 14 low-fibre
coordinates; all of f0..f13 fail as relations. This accounts exactly for
Z8b's 8-limb residual. The designer's §2.5.1 may be right in the monomial
basis and simply mis-applied to coefficients in the encoder's basis
(`basis::values`, NaturalBasis); that is the agent's hypothesis and is not
checked. G-low is 220, not 224, because G's extra claim is a functional on
exactly the rows π⁻¹(0..55); it is 224 without it. The assembly holds:
bat(D-high_bal ∩ ker own_D) + bat(G ∩ ker R_G ∩ ker own_G) = 1,912 on every
structure. PR6 and PR7 hold.

**D21.6 Consequence for the Lean statement.** (Q′) and the (B) target are
fixed by D21.2. The proof of (B) cannot use the x^28 coordinate split, and the
Lean statement of the D-high/G decomposition is not written until the basis
question is answered. Z8d is issued:

1. Identify the coefficient basis of the D word in Lean (`R0Z/MaskLayout.lean`
   `dWord` and the PCS encoder it feeds) and in the probe (`encoder::eval_pair`,
   `basis::values`), and the change of basis to monomials.
2. Rerun the D-high block with the condition "monomial-basis polynomial
   divisible by x^28" (and with "NaturalBasis coefficients < 56 zero", as a
   control equal to Z8c's 1,808). Report the rank, the left kernel modulo the
   25 relations, and whether f0..f13 hold.
3. Rerun G-low in the same basis, with and without G's extra claim.
4. Structure A, vectors 0–4; one job per vector; MemoryMax 4G; same receipts.

If (2) gives 1,800 with f0..f13 holding, §2.5 stands in the monomial basis and
D21's Lean statement is written in that basis. Otherwise the designer revises
§2.5 from Z8c §5's remainder support [h2..h6, f22..f255].

J1–J3 and J5a of the T2b-2b plan do not depend on §2.5 and can be released.
Verdict unchanged. Host counter: next 3426.

### Lead acceptance of Z8d (2026-10-15); D22: §2.5 of the T2b-2b design withdrawn, (B) redesign issued

Z8d (`de86b2306`, Opus agent; `z4/FINDINGS-Z8d.md`) is accepted. The control
reproduces Z8c's 1,808 exactly. Structure A, vectors 0–4, identical outputs.
Receipts: all exit 0, swap 0, peak RSS 340 MB per job, cgroup peak 1.69 GB
under MemoryMax 4G; 210 source hashes and 5 CHALLENGE lines match.

**D22.1 Basis.** Lean and Rust both index the D message (and every PCS
message) in the natural Chebyshev-product basis N_j = ∏_{b ∈ bits j} T_{2^b}:
`dWord` (MaskLayout.lean:91) → `coeffsLinear` (HonestView.lean:80, π only) →
`naturalCoefficientPolynomial` (V5FriInitialCircleEncoderIdentity.lean:124;
CircleNaturalBasis.lean:43); `foldMessage` reads natural coordinates directly
(Fold.lean:71). Rust: encoder.rs:10, basis.rs:37, fold.rs:61.

**D22.2 §2.5 of the design is withdrawn.** It treats c as monomial
coefficients. Its quotient step is a correct polynomial fact, but the
conclusion that f0..f13 vanish needs natural coefficients of the quotient
below 56 to be zero, which X^28-divisibility does not give (checked: natural
low coefficients 56/56 nonzero, low folds 14/14 nonzero). In the monomial
condition D-high reaches 1,792, not 1,800 (1,700 inside ker R_D, where it is
not round-free: R_D rank 216). No basis gives the design's split.

**D22.3 What stands.** (Q′), the (B) target (D21.2: bat(ker own) is the common
zero set of the 25 relations) and the assembly: every D-high variant plus G's
batched image reaches 1,912 = bat(ker own). G-low is 224 in monomial
coordinates with or without the extra claim. The remainder support
[h2..h6, f22..f255] is the complement of the 25 relations' pivots and carries
no structure; D21.6's instruction to revise from it is withdrawn.

**D22.4 Host discipline.** The full run launched while another job's scope (a
`timeout 900` Lean replay of aspis-r1-concrete-decoder) was active; the launch
listed scopes but did not gate on them. No harm (4 GiB reservation, the other
scope exited within moments), but the rule is unchanged: a launch gates on no
other aspis scope being active, or on an explicit reservation sum check.

**D22.5 Next.** A design revision of (B) (T2b-2b-D′, Opus agent) in the natural
basis. Requirements: every claimed rank reproduces Z8c/Z8d on structure A;
the decomposition must be one Lean can state (row sets or natural-coordinate
conditions on named words, not dense change-of-basis conditions unless a
closed form is given); if no proof route is found, (B) enters the theorem as
an explicit numerically checked premise, labelled in the ledger alongside
OT-open, and the design says so. D21's Lean statement waits for it. J1–J3 and
J5a remain releasable. Verdict unchanged. Host counter: next 3426.

### Lead acceptance of T2b-2b-D′ (2026-10-15); D23: (B) enters as premise B-open; privacy claim stays conditional

T2b-2b-D′ (`93e0830da`, Opus agent; `t2b2b/DESIGN-T2b-2b-Dprime.txt`, probe
Z8e in `z4/z8e.rs`, `z4/z8e-runs/`) is accepted as the working design.
Z8e receipts: structure A, vectors 0–4, all exit 0, swap 0, peak RSS 324 MB
per job, cgroup peak 1.42 GB under MemoryMax 4G, launches gated on no other
aspis scope (D22.4 satisfied), 211 source hashes match.

**D23.1 D-high explained.** In the natural basis, V_D = B₀ ∩ {f0..f13 ∈
lowShadow} ∩ ker etaRel 28 (1,912 − 96 − 8 = 1,808). "⊆" is argued in the
design (Facts 1–2: multiplication by the chord line moves natural indices up
by one or down only by clearing trailing ones; the conjugate round_eval
relation); "=" is measured (annihilator 304 limbs = 25 relations + 96 Ψ_lo +
8 etaRel, unexplained 0). V_G = B₀ ∩ ker etaRel 27 exactly (1,904). This
replaces the withdrawn x^28 law.

**D23.2 (B) is not proved for all query sets.** It reduces to DHighChar⊇ and
GCover; the query-dependent parts (TP_D and Gb) have the same obstacle as
OT-open (fixed or row-side functionals must stay independent of the opened
evaluations at 22 arbitrary fibres; the dense inactive-row sum rules out the
obvious uniform witness). The T2b-2b theorem takes `hBc : BCond` as a named
hypothesis; narrower forms (assembly, DHighChar⊇ ∧ GCover, Ga ∧ Gb) are J7′
lemmas so the theorem does not change when a piece is later proved.

**D23.3 Ledger status.** B-open and OT-open are carried together as the
"transversality premises" family, each checked numerically on the stated
vectors and **with no failure-mass bound**. A premise checked on 35 challenge
vectors is evidence, not a bound on the probability over the verifier's query
draw. Therefore the R0 privacy result, once J1–J9 land, is: statistical HVZK
and ZK_FS with the stated ledger terms **conditional on the transversality
premises**. No release text may state unconditional statistical
zero-knowledge until those premises carry a proved mass bound or are removed
by a mask-design change. The new conditional rows (C_ll invertible, GoodWrap,
G2, Ga, γ ∉ K₄, σ) enter the ledger only if BCond is later discharged by this
route. Good₃ is unchanged.

**D23.4 Job order.** J1, J2, J3, J5a unchanged and releasable; J4 next; J7 is
replaced by J7′ (`R0Z/BatchedBlock.lean`, structural, writable before J5b–J6);
J7a (`R0Z/NaturalShift.lean`, symbolic, needed only to narrow the premise);
J5b, J5c, J6 unchanged; J9 takes hBc and the Q′ premises; J10 is the research
item for TP_D, Gb and the transversality bound. The two Lean premises the
route assumes (T_{2^k}(node) ≠ 0 at the line nodes; transport identity on rows
≥ 479) are recorded as J7a/J10 obligations.

**D23.5 Open for the user.** Removing the transversality premises by a
mask-design change (extra mask randomness on D/G sized to the 22 openings) is
a protocol change, not a proof task; it is listed, not decided.

Verdict unchanged. Host counter: next 3426.

### Lead acceptance of the (ii′) design as a proposal (2026-10-17); D24; R1 retargeting

The privacy agents issued on 2026-10-17 work for R1. R1 is the deployment
target, and R0Z is only the name of the track. Payload-generic work (T2a,
ZF-A, J1, J3, J5a) carries over to R1. Rank facts and J2/J4 do not carry over
until Z9 restates them for the R1 payload. Five Opus agents are running, on
branches codex/r0-{z9-r1-payload, k4-silent, hermite-span,
transversality-study, clause-iiprime}-20261017. Attempt ranges: J1/J3
3426–3459, J5a 3460–3489, (ii′) 3490–3499.

The (ii′) design (`t2b2b/DESIGN-ii-prime.txt`, worker 596b371d0, fast-forward
from 524e1debb) is accepted as the working design. No Lean was run and no
attempts were used.

**D24.1 (ii′) as written is false.** `MaskImageOn` clause (ii′) (Shift.lean:190)
quantifies over every `w, w'` with `h.public w = x.1`, and `HonestProver` has
no validity field. The initial-sum functional and `.inactiveSum` vanish on
range A but separate a satisfying trace from a non-satisfying one with the
same public value (counterexample in design §1.4). The lead checked
Shift.lean:180–191 and Z4Maps.lean:62. The fix (§1.5) needs no edit to any
proved module. Define `HonestValid` (laneOf plus the two helper sums) and
apply `MaskImageOn` to the restricted prover `h.restrict V`, where V is
validity on P. The T2a/ZF-A theorems then apply verbatim. Restricting to valid
witnesses is the standard ZK quantifier (x, w) ∈ R. Builder completeness
(honest builds satisfy HonestValid) is a new obligation, J0b.

**D24.2 `c1_surjectivity` is insufficient.** It omits `.extraClaim c` for
c < 16 and the H1 lane. It is replaced by the premises `C1Lift` and `H1Lift`.
The opened-symbol part (88 limbs per lane) is STRUCTURAL under D13Order with
≤ 22 queries (Vandermonde on the quarter polynomials). The remaining 24 limbs
per lane are carried as C1T-open and H1T-open. Both join the D23
transversality family, so the privacy claim stays conditional on that family.
H1Lift has never been measured on its own, so the J11 numeric check comes first.

**D24.3 The (B) premise.** The design proposes `BReach := B₀ ≤ bat(ker own ⊓ ker R)`
(which implies BCond) as the single (B) premise for both clauses. This is
deferred until Z9 restates B₀ for the R1 opening layer (no chord quotient,
two fold layers, 64 final values, 88 extra folded-word openings). Z9's first
report already says the R0 Ψ_lo/etaRel structure does not transfer.

**D24.4 R1 transport.** Under S2's π_R1 (D18, identity digit maps), the
eligible semantic coefficients are a top block (quarter index 208–255), not a
prefix. The opened part of C1Lift is therefore not structural on R1 as built.
Two ways out: Variant D (the D13 transport), or a digit-map search (J11b).
Both are protocol choices. They go to the user together with D23.5, once the
transversality study lands.

**D24.5 Job order.** J0/J0b, J4′, J13–J16 and J11 are listed, not issued. They
wait for Z9 and the D23.5/D24.4 decisions. Verdict unchanged. Host counter:
next 3426 (ranges above).

### Lead acceptance of J5a (2026-10-17); D25

J5a `R0Z/HermiteSpan.lean` is accepted. The worker commits are ced2b82d9 and
f4e3af77d, cherry-picked here. The file imports Mathlib only and is generic
over the field, so it applies to R1. Host attempt 3462: exit 0, 12.06 s,
peak RSS 6,604,012 KiB, 0 swaps. The source SHA `e9ff8cf7…` matches the
committed file. All 26 `#print axioms` lines are exactly
`[propext, Classical.choice, Quot.sound]`, verified by the lead from the host
log. The file has no sorry, axiom or native_decide. Attempts 3460 and 3461
were compile errors (exit 1) and are retained in the evidence.

**D25.1 P3 restated.** The design's P3 claim dim span{Φ_i, X·Φ_i} = min(2n, 28)
(DESIGN-T2b-2b.txt:401–402) is false for some distinct nodes. Two exact
counterexamples:
- m=2, n=2 over GF(5), β=(0,1): rank 3;
- m=26, n=14 over GF(101): rank 27.

The two lowest coefficients become tied to the nodes once 2n ≥ m+1. The
proved forms are:
- P3a, span{Φ_i}: unconditional;
- P3b, span{Φ_i, X·Φ_i}: covers degrees ≥ 2, i.e. r ≤ min(2n, m), with
  independence for 2n ≤ m.

Every citation of P3 in the design (lines 410, 430, 454, 462, 535, 806) uses
P3a or P3b with n ≤ 8, inside the proved range. The D′ design does not cite
P3. J5b and J5c must cite the restricted forms by name.

**D25.2 Process.** The worker launched 3462 while its own check had counted
one other Lean process. run2.sh's flock serialised the two, and the run took
12 s. This is a gate lapse; it is recorded and is not repeated.

### Lead acceptance of J1 and J3 (2026-10-17); D26

The worker commits 3619dde1a and 1c957c01f are cherry-picked here. The lead
verified both host receipts:
- `R0Z/K4.lean`: attempt 3427, exit 0, 10.9 s, peak RSS 6,697,960 KiB,
  0 swaps, SHA `d588952a…` (matches), 28 axiom reports;
- `R0Z/SilentReduction.lean`: attempt 3437, exit 0, 10.6 s, peak RSS
  6,812,272 KiB, 0 swaps, SHA `99fc4a68…` (matches), 17 axiom reports.

Every axiom line is exactly `[propext, Classical.choice, Quot.sound]`. There
is no sorry, axiom, admit or native_decide. Evidence for attempts 3426–3437
is in `t2b2b/evidence-J1-J3.json`.

**D26.1 What is proved.**
- K₂/K₄ subfields, with `finrank_K4F = 4` and `finrank_K2F = 2`.
- `mem_K2_of_quadratic`, for all x, without a card premise.
- `Lambda F a j`.
- `Good3` in the D21 form (LOG line 4274).
- `lambda4_eq_K4`.
- `exists_silent_of_cover`, `ia_pure_zero` and `ms_pure_eq_initial`.
- `QPrime` and `BCond`. BCond is in exactly the D23.2 form; the lead checked
  SilentReduction.lean:248.
- `chain0K4_le_silent_of (hQ : QPrime) (hBc : BCond) : Chain0K4 ≤
  (silentMasks π B ch).map (A ∘ inlM)`.

This is the (Q′)+(B) reduction as a theorem. T2b-2b on R0 is now J2 plus the
two transversality premises. One gap is recorded: `ownMap` keeps all 29
columns, so its kernel being the per-lane own kernel (extra columns 0–15 and
26 zero on mask tapes) is not proved. Any later lemma that uses the per-lane
form must prove that equivalence first.

**D26.2 Carries over to R1:** the subfield/Λ/quadratic facts and
`exists_silent_of_cover`. Written against the R0 payload, and to be restated
after Z9: `Good3`, `lambda4_eq_K4`, ownMap/batMap, ChainT0, QPrime, BCond
and the reduction. These are template statements for the R1 restatement.

**D26.3 Violations (recorded by the worker).**
- 3428 was launched while the Z9 preflight scope was active, with the gate
  check and the launch in one command.
- 3428 then hit Lean's own -M7000 memory exception: a full `simp` unfolded
  the copy-row tables. The source was changed before any rerun, and no cap
  was raised.

Lead exception (2026-10-17): Lean may run beside a capped non-Lean probe scope
(≤ 4G, swap 0) when run2.sh's reservation check passes and no other Lean, R1
or extraction job is running. The gate check must be a separate command whose
output is read before launch.

Lesson for generators and proofs: state balance-cancellation lemmas K-valued,
with decidability instances passed in rather than synthesized. Keep `simp`
from unfolding `PayloadSplit.L`. Instance-path mismatches made the kernel
reduce `copyInactiveRows`.

### Lead acceptance of Z9 (2026-10-17); D27: the privacy reduction transfers to R1

Z9 (worker commits 96b37aa83..8c26ef3e9, cherry-picked) is accepted. The R1
payload was taken from spend-path tip 1822c2ced, variant S2. The
expectations were committed (7ab695866, 11:19) before the preflight results
(bb10719b2, 11:27). The full run took 29:58.6 for 40 jobs: structures A, B, I,
J × vectors 0–4 × the checkpoint's two γ limb sets. All exited 0, with peak
child RSS 225,940 KiB, cgroup peak 1.126 GB, 0 swaps and caps 3G/4G/swap 0.
All CHALLENGE lines replay. The lead read the summary: for A, structure
vector 0, γ set 0, the chain basis gives image rank 1,076 with 0 failures,
and B0 has annihilator 384 = 384 explained by the 48 relations, with 0
unexplained.

**D27.1 R1 payload differences.** The R1 payload differs from R0 in five ways:
- transport D18 instead of D13;
- no chord quotient: OOD enters as weight kinds 5 and 6;
- two folds;
- the batched view is 167 E values (1,336 limbs) against R0's 2,112;
- 48 verifier relations against R0's 25.

ρ enters no disclosed coordinate. The semantic layer (rows 0–26, masks,
balancing, terminal, chain target) is the same as R0's. Model checks pass,
including every verifier equation on a full honest view.

**D27.2 Gate on R1.**

| Structures | Silent rank | (i′) | (ii′) |
|---|---:|---:|---:|
| A, J | 1,076 | 25/25 | 25/25 |
| B | 1,038 | 0/25 | 25/25 |
| I | 1,068 | 0/25 | 25/25 |

The B and I deficits have the same pivots as Z8/Z8c, so Good₃ stays the
predicate. This is numerically checked, not proved.

**D27.3 Structure of (B) on R1.** The (Q′)+(B) reduction transfers to R1:
- The round image of the own-silent kernel, with initial sum zero, is 1,076
  and contains Chain0₄.
- B0 = 1,336 − 384 = 952. The annihilator is exactly the 48 relations.
- BCond holds (952 = 952) in all 40 jobs.

There is no Ψ_lo/lowShadow or etaRel analogue:
- D-high's deficit is the exact law f0 = f1 = f2 = 0, giving V_D = 928.
- V_G = B0 = 952.

So on R1, BCond reduces to "G alone covers B0" (`V_G = B0`). The D-high/G
assembly of D23 is not needed. This is simpler than R0, and it is the form the
R1 restatement of J3 and the transversality work must target. As on R0, the
PCS block is not full rank (1,304 of 1,712).

**D27.4 Still open.**
- B-open (now `V_G = B0` on R1) and OT-open are evidence from 40 jobs, with
  no failure-mass bound.
- γ was tested only on the two fixed limb sets.
- Structures K, L, M and the per-lane OT′ checks were not rerun on R1.
- Salted leaves and paths are outside the linear model.
- The source has moved since 1822c2ced through extraction-only refactors
  (Digest32, unrolls), which do not change mask layout or weights.

Next: restate J1/J3's payload-specific statements for R1 (Good3 layout,
ownMap/batMap over the R1 view, BCond_R1 := V_G = B0). The J2/J4 analogues
for R1 wait on that, together with the D23.5/D24.4 decisions.

### Transversality study received (2026-10-17); D28: D23.5 options for R1, decision pending with the user

`t2b2b/STUDY-TRANSVERSALITY-R1.txt` (worker b84c2ae82..1301fb31f,
cherry-picked) and probe Z10 (`t2b2b/z10/`) are received. Z10 ran 34 jobs,
all exit 0, in 18:47, with per-job peak RSS ≤ 17.5 MB and 0 swaps. Its launch
waited for the Z9 and c-source25 scopes to finish. Z10 is an R1-sized
single-lane model, not the R1 payload. It found 0 failures in 13,000 query
sets. The forced-dependency control failed 20/20 as intended. A
failure-free result of that size bounds the failure rate only below
≈2.3·10⁻⁴.

**D28.1 Route P (prove the premises) is not a main line.** Per-query-set
Schwartz–Zippel needs a witness challenge for each of ≈2^306 query sets, and
the explicit candidates collapse the round rank. Fibre counting gives
≈2^-1.5. The query-free Hankel route certifies only ≈5 functionals against
the ≈400–1,900 needed. The study estimates under 15% chance of a proved bound
within weeks.

**D28.2 The options (CU figures are estimates, ±1.5×; none measured):**
- **M1:** a uniform E-valued Z lane in the FRI batch. It removes B-open with
  a short argument valid for every challenge and query set. Cost: +3,040
  proof bytes and ≈ +24–69k CU. Z's seven pairing values must be bound
  before γ; the study found and fixed this soundness trap in its own draft.
- **M2:** Libra on D extended to all ten rounds, plus an evaluation
  reservoir. It removes OT-open and Good₃'s round-cover condition. Cost:
  0 bytes and ≈ +40–78k CU, all in tx2, which has 31.5k headroom in the
  worst settlement. One query-free determinant remains, with mass ≈2^-114.
- **M3:** honest-prover rejection.
  - After the challenges are drawn, the prover evaluates
    P := Good₃ ∧ OT ∧ BCond_R1 ∧ C1T/H1T, using exact linear algebra on
    public data. If P fails, it discards the attempt and restarts with fresh
    masks, salts and attempt secrets.
  - P depends only on the challenges, which in the ROM are uniform and
    independent of the witness. So the accept decision leaks nothing, and
    the simulator rejection-samples the same P.
  - Costs: verifier CU 0, proof bytes 0, soundness rows unchanged, and
    badMass(P) leaves the privacy error entirely, including Good₃'s mass.
  - What it requires:
    - an abort-aware ZK_FS statement, in ZF1's scope, taking the
      eprint 2023/245 FS-with-aborts caution into account;
    - a prover-side rank check per attempt (seconds on a desktop);
    - a refinement obligation: the Rust check decides exactly the Lean
      predicate P on the exact R1 payload;
    - the honest prover never publishes a ¬P transcript, with a cap on
      attempts and an explicit failure exit.

**D28.3 D24.4 may not need a protocol change.** This is the study's
observation and has not been checked. The top block 208–255 contains the
aligned sub-block 224–245. There N_{224+e} = N_224·N_e for e < 22, so the
22-node system is a diagonal scaling times a Vandermonde, invertible for
every query set, given NZ for k = 5, 6, 7. Classes 2 and 3 need an
eligibility-registry check. Variant D would bring back the transport cost
that D18 removed, so it is not affordable. Lead check pending.

**D28.4 Lead view.** M3 is the right default. The verifier is unchanged, so
soundness, CU (stage1 is already over 1.3M) and every R1 proof are
untouched. The privacy statement becomes unconditional apart from
oracle-programming terms. Its new obligations (the abort-aware ZK_FS and
the Rust predicate check) are ordinary proof work rather than open
research. M1 and M2 stay as fallbacks if the abort-aware composition fails.
Decision D23.5 belongs to the user.

### D29: user decision on D23.5 (2026-10-17): honest-prover rejection (M3) now; Route P later

**D29.1 Decision.** The user chose M3: the honest prover rejects bad challenges.
Route P, a proved failure-mass bound for the transversality premises, is
kept as later research, not abandoned. M1 and M2 remain fallbacks if the
abort-aware composition fails.

**D29.2 The predicate P.** P is the conjunction of every challenge condition
the privacy proof uses. The lead checked that each conjunct is defined from
π, B and ch only: `QPrime` (SilentReduction.lean:241), `BCond` (:248), and
`C1Lift`/`H1Lift` (DESIGN-ii-prime §2.1). Each is therefore a function of
public data. P includes:
- `QPrime_R1` and `BCond_R1` (on R1, V_G = B0);
- the J2 side conditions (sem ∈ K₄, α₉ ≠ ½);
- `C1Lift`, `H1Lift` and `BReach` for clause (ii′).

QPrime and BCond are checked directly, not derived from Good₃. So J5b, J5c,
J6, J7′, J7a and J8 leave the critical path. They come back only for Route P.

What remains on the critical path: the R1 privacy model, J2-R1, (ii′) (J0,
J0b, J4′, the residual and lift steps), the abort-aware ZK_FS (ZF1), the
efficient simulator (ZF2), and the Rust predicate check with its refinement.

**D29.3 Requirements on the honest prover.**
- It never publishes a transcript with ¬P.
- Attempts use fresh masks, salts and attempt secrets.
- Attempts are capped, with an explicit failure exit.

The failure exit depends only on challenges and publishes nothing. Its
probability matters for liveness, not privacy. There is no proof that
Pr[¬P] is small, and Z8–Z10 have observed no failures.

**D29.4 First jobs.**
- **R1M:** an inventory and plan for the R1 privacy model, deciding which
  R0Z/R0P definitions are payload-specific and the minimal Lean model of the
  Z9 payload.
- **ZF1-abort:** the abort-aware ZK_FS, generic over FSExperiments, building
  on ZF-A. Attempts 3500–3549.

The Rust predicate check waits for R1M's definitions.

### Lead acceptance of the R1 privacy-model design (2026-10-18); D30

`t2b2b/DESIGN-R1-PRIVACY-MODEL.txt` (worker 0b36b12bf..eb6c3e476,
cherry-picked) is accepted as the plan for proving privacy on R1.

**D30.1 Findings accepted.** R1 differs from the proved R0Z model only in
the batched opening block. The per-lane, semantic and mask layers are the
same. No proved theorem uses `D13Order`: the lead grepped R0Z and R0P, and
it appears only as a definition in HonestView.lean. So D18 is an instance
choice. On R1, GoodCircle, Good3 and GoodAlpha are not needed.

**D30.2 Decision: refactor, not copy.** `PayloadCell` takes the batched
cells as a parameter (`Bat`), with a `BatchedLayer` class. R0 and R1 are
instances. About 20 proved R0Z modules are re-sourced and recompiled once
each. Acceptance for R1-0: every previously listed `#print axioms` line
reappears with the same theorem name and the standard axioms, and no
statement changes except the `Bat` parameter. The lead diffs the statements.
`hvzk_on_of` (HVZK for any P) is added.

**D30.3 Target.** `P_R1 := HalfOK ∧ SemK4 ∧ QPrime_R1 ∧ BCondG_R1 ∧ (∀ c,
C1Lift c) ∧ H1Lift ∧ QueryCard`. BCondG_R1 is `B0R1 ≤ V_G`, which with
J4-R1 gives both BCond and BReach. The target theorem is
`maskImageOn_R1 : MaskImageOn (Bat := R1Bat) (P_R1 …) (h.restrict (ValidOn …)) B x`,
for every π. J14-R1 (the structural opened part) is deferred to Route P,
because C1Lift is a conjunct of P.

**D30.4 R1-1 (opening-layer mirror).** The worker brings the spend-path
files listed in §4 into its own branch by `git show`, unchanged, with source
SHAs recorded. The spend-path branch itself is not touched.

**D30.5 Riskiest item.** J4-R1's `line_identity`: the second fold on the
line domain commuting with the encoder. It is also open on the R1 soundness
side. The fallbacks are `B0own ≤ V_G` for clause (i′) and a trace-space rank
check in P for clause (ii′).

**D30.6 Issued, ordered by lanes.**

| Lane | Job | Attempts |
|---|---|---|
| A | R1-0 | 3550–3619 |
| B | R1-1, then J4-R1(a) (payload-free) | 3620–3679 |
| D | Z9b numeric: relR1 as written annihilates bat(ker own); C1Lift and H1Lift on their own | Rust, capped |

ZF1-abort continues on 3500–3549. Estimate: 15–25 worker-days and 90–170
attempts, about 10–15 days elapsed. J0b is unestimated.

### ZF1-abort completed — abort-aware ZK_FS without badMass (2026-10-18)

Branch `codex/r0-zf1-abort-20261017`, base `a4246222a` (D29). Design in
[zf1/DESIGN-ZF1-ABORT.txt](zf1/DESIGN-ZF1-ABORT.txt); Lean in
`lean/R0Z/FsAbort.lean` (imports `R0Z.FsGood` only; no PayloadCell
constructor is used). Proved: in the retrying middle games (per-attempt
coins and tapes, least accepted attempt, cap N, failure output) only
P-challenges reach the view and the simulator, so `HVZK_on P` makes the
middle means equal (`middleAbort_means_eq`); hence
`zkfs_of_hvzk_on_abort : HVZK_on P → AbortReductionWith P … ab x ε_real
ε_ideal → ZK_FS … (ε_real + ε_ideal)` with no badMass term, and
`zkfs_of_hvzk_on_abort_terms` splitting the reduction into the named
identical-until-bad events Hit (adversary reads a discarded attempt's
address), Coll (prover-address repetition within or across attempts) and
Prog (inconsistent programming of the accepted attempt), error
ε_hit + ε_coll + ε_prog. The couplings and the three bounds are payload
hypotheses (ZF1a/b), not proved. The failure exit costs nothing. The
eprint 2023/245 difficulty (secret-dependent aborts) does not arise because
P depends on ch only; the PDF was not readable from this session (HTTP 403),
only the abstract. Requirement R-fresh (fresh attempt material in each
attempt's first absorbed block) must be checked on the R1 layout.
Host attempts 3500 (exit 1), 3501 (exit 1, diagnostic), 3502 (exit 0,
4.35 s, peak RSS 6,770,592 KiB, 0 swaps); all 20 axiom lines standard;
evidence [zf1/abort-evidence.json](zf1/abort-evidence.json). Next host
attempt in this range: 3503.

### Lead acceptance of ZF1-abort (2026-10-18); D31

ZF1-abort (worker 2542546f2..746e7204d, 11 commits, cherry-picked) is
accepted.
- `R0Z/FsAbort.lean` imports only `R0Z.FsGood` and uses no PayloadCell
  constructor, so it applies to R1 unchanged.
- Host attempt 3502: exit 0, 4.35 s, peak RSS 6,770,592 KiB, 0 swaps. The
  source SHA `9b1ffc92…` matches. All 20 axiom lines are exactly the standard
  three (lead-verified from the host log). The file has no sorry, axiom or
  admit.
- It compiled against the ZF-A objects 3408/3409, whose sources are
  byte-identical to the base. Attempts 3500 and 3501 failed to compile and
  are retained.

**D31.1 What is proved.**
- `zkfs_of_hvzk_on_abort : HVZK_on P → AbortReductionWith … → ZK_FS …
  (ε_real + ε_ideal)`, which has no badMass P term.
- `zkfs_of_hvzk_on_abort_terms`, which gives ZK_FS with error
  ε_hit + ε_coll + ε_prog from a real coupling (Hit and Coll) and an ideal
  coupling (Prog).
- The generic retry core: `firstGood`, `retry_means_eq`,
  `until_bad`/`eventMass_or_le`.

The simulator runs the same capped loop on the same public P, so ch | P is
sampled at the honest prover's own cost. The eprint 2023/245 failure mode
(aborting on secret-dependent responses) does not arise: P is a function of
ch and public data, which the type of `HVZK_on` enforces. Aborted
transcripts are never published, and Hit charges their oracle entries. The
worker read only the paper's abstract, so a full-text check stays on the
review list.

**D31.2 Open.**
- The two couplings for the concrete retrying sponge games. These are ZF1a/b,
  per-attempt.
- Numerical bounds on ε_hit, ε_coll and ε_prog.
- ZF2, the efficient simulator.

Each attempt's first absorbed block must contain fresh attempt material,
otherwise Coll has mass 1. On R1, row 0 absorbs the C1 root (LOG/TARGET
note), which is over freshly salted leaves. So this holds if salts are
fresh per attempt. That becomes an honest-prover requirement, together
with D29.3.

**D31.3** R1-0 may now proceed with host overwrites (D30 sequencing). The
lead recompiles FsAbort once after R1-0's ordered pass.

### Lead acceptance of R1-0 (2026-10-18); D32: payload parametrised over the batched block

R1-0 (worker aa8a9a746..01e1f84d5, 19 commits, cherry-picked) is accepted.

**What changed.**
- `PayloadCell Bat` with `class BatchedLayer K Bat`.
- A new module `R0Z/R0Batched` holds the R0 instance. Its read is the old
  `linearPayload` branches word for word.
- 14 modules take `{Bat} [BatchedLayer K Bat]`.
- `hvzk_on_of` (HVZK for any P) is added in Shift.

**Final ordered pass.** Attempts 3585–3605 compiled 21 modules into
objects2, all exit 0, with 0 swaps and peak RSS 6.73–6.93 GB. The lead
spot-checked HonestView 3585, Shift 3596, SilentReduction 3601 and
FsAbort 3605: the host SHA matches the committed source in each. Across
3585–3605 every reported axiom line is `[propext, Classical.choice,
Quot.sound]` (156) or `[propext, Quot.sound]` (5). The 165 previous lines
all reappear with the same theorem names, and there are 4 new ones. The
overlay attempts were 3550–3584. The snapshot `$T/backup-pre-R1-0` has 62
files, with its manifest committed.

**D32.1 Rulings on the departures.**
- `[Fintype Bat]` on the 11 law-using theorems is accepted. R0Bat is finite,
  and R1Bat (round0 7, round1 7, folded openings, final 64) is finite too.
- Leaving out `[DecidableEq Bat]` is accepted, following the memory rule
  in D26.3.
- The three non-mechanical edits are accepted: `PayloadCell`;
  `messages : Payload K R0Bat` (the R0 32-row schedule; R1's 33-row
  schedule is separate work for ZF1); and `batMap : … → (Bat → K)` with
  BCond's text unchanged.
- FsAbort was re-sourced with the Bat parameter. It compiled at 3605 with
  all 20 axiom lines unchanged, which replaces the lead's planned
  recompile.

**D32.2 Next.** R1-2, the R1 instance `R1Bat` and its `BatchedLayer`, is
unblocked. The host overlay directory `$T/r1-0` may be deleted.

### Lead acceptance of R1-1 and J4-R1(a) (2026-10-18); D33: line_identity proved

The worker commits fa68ccb85, 1f4bb35e2, 2cee2f9e8 and cf23977a1 are
cherry-picked. Attempts used: 3620–3631. Evidence is in
`t2b2b/evidence-R1-1-J4R1a.json`. The mirror manifest is
`t2b2b/R1-1-MIRROR.json` (spend-path tip e38279522).

**D33.1 J4-R1(a) `R1Z/BatchedAlgebra.lean` is accepted.** Host 3628: exit 0.
The SHA `f4e7aa79…` matches. All 13 axiom lines are standard (lead-verified).
The file imports only R1Mirror.FoldCoefficientBridge and BaseRepeatedLift.
It proves `s2b_identity`, `s1_identity`, `s2a_identity` (for any seven
functionals combined with κ powers), `circ_identity` with
`circ_zero_of_fibre_zero`, and **`line_identity`**. The last one, the
design's flagged risk, is the second fold of the four stored children
equalling `secondLinear (coefficientFoldLayer 64 α₁ m) v` for every m and
α₁. `line_layer_identity` is the whole-layer version.

The public inverse table is `lineInverse = ((2x)⁻¹, −(2y)⁻¹, (2z)⁻¹)`. This
is the same normalisation Z9b found independently: relR1 annihilates
bat(ker own) only with this table. The two findings agree.

Open refinement items:
- `storedFirstLineX18` versus the Rust `line_node`;
- `lineInverse` versus `QueryGeometry`.

**D33.2 R1-1 mirror.** Of 12 files mirrored unchanged except import lines
(R1Mirror.*), 9 are green. Line18Geometry fails under this workspace's
-M7000 cap (attempt 3625: kernel out of memory on 5 theorems, 7.17 GB) and
contains `set_option maxRecDepth 20000`. ConcreteProjection and
SecondFoldRestoration import it. These three are NOT accepted here, and
nothing accepted depends on them. They are not to be rerun unchanged or
under a raised cap.

**D33.3 Interference.** Attempt 3623 launched beside the R1 worker-C serial
runner, whose guard killed its own attempt (selected-sigma …Core-5, exit
−9). After that the worker gated on a fully idle host. This is the third
recorded launch-gating lapse (D25.2, D26.3). The rule stands: gate and
launch are separate commands, and any Lean process on the host means wait.

**D33.4 Next.** R1-2 (`R1Z/Batched.lean`, the R1 instance) then J4-R1(b)
(relR1, B0R1, `bat_L_mem_B0R1`). Both are now unblocked: R1-0 is D32 and
the algebra is D33.1.

### Lead acceptance of R1-2 and J4-R1(b) (2026-10-18); D34: J4-R1 closed

The worker commits 9398aa8a1 and 56ad2ce12 are cherry-picked. The lead
verified both host receipts:
- `R1Z/Batched.lean`: attempt 3681, exit 0, SHA `fd43a244…` matches,
  17 standard axiom lines;
- `R1Z/VerifierRelationsR1.lean`: attempt 3683, exit 0, SHA `3fc38a95…`
  matches, 13 standard axiom lines.

Neither file has sorry, axiom or a maxRecDepth/maxHeartbeats override.
Attempts 3680 and 3682 were elaboration failures. Evidence:
`t2b2b/evidence-R1-2-J4R1b.json`.

**D34.1 Proved.**
- R1Bat, with `instance BatchedLayer K R1Bat` and the seven `ell`
  functionals, each equal to the γ-batch of its own cell.
- relR1 with the D33 `lineInverse`, and B0R1.
- `bat_L_mem_B0R1` for every trace whose own cells and inactive sum vanish
  (J4′ form; the own-cell conditions are explicit hypotheses).
- **`bat_ker_own_le_B0R1`**, with no challenge premise: there is no
  GoodCircle on R1.

So "BCondG_R1 ⇒ BCond ∧ BReach" depends only on R1-3. The proof lesson
from 3680 is recorded: make `dotLinear` and `roundPolynomialLinear`
irreducible after their apply lemmas, and never prove `ell` cells by `rfl`.

**D34.2 Memory headroom.** Peak RSS of 6.78–6.93 GB is within 70–250 MB
of Lean's -M7000. Later R1Z modules must import narrowly (only what they
use). The cap is not raised. A module that hits it is split.

**D34.3 Open refinement items.**
- `storedFirstLineX18` versus the Rust `line_node`;
- `lineInverse` versus `QueryGeometry`;
- `ell` versus the Rust weight kinds 5/6 (numerically checked by Z9 only).

**D34.4 Next.**
- Lane A: R1-3 PredicateR1, then J2-R1 (relations worker, attempts
  3684–3739).
- Lane C: J0 and J13-R1 (a new worker, attempts 3740–3799).

### Lead acceptance of Z9b (2026-10-18); D35: B0R1 corrected, C1Lift/H1Lift measured

Z9b (worker 4ecdc28f0..12dc399ac, cherry-picked) is accepted. The
expectations were committed before any run. 253 jobs (506 evaluations, both γ
limb sets) were run on the real R1 payload:
- the Z4c actual query sets;
- {0..21}, spaced and paired sets;
- 200 uniform sets;
- 20 consecutive and 20 coset sets.

The full run took 1:02:09, with cgroup peak 733 MB and 0 swaps. One
thread-spawn failure (TasksMax 64, not memory) was rerun alone at
concurrency 1 without raising caps, and passed. Everything here is numerically
checked, not proved.

**D35.1 lineInverse (F1).** Only `((2x)⁻¹, −(2y)⁻¹, (2z)⁻¹)` makes relR1
hold. The literal (1/x, 1/y, 1/z) mismatches 88/88, and the unsigned form
mismatches 44/88. This agrees with the table D33's `line_identity` was proved
with. With it, ia + relR1 annihilates bat(ker own) exactly in all 506
evaluations, with 0 unexplained.

**D35.2 BCondG_R1 as typed is false (F2), and is corrected.** B0R1 =
ker relR1 over all of R1Bat leaves the 262,144 − 4P unopened folded cells
free, while V_G is zero there. Correction: B0R1′ := B0R1 ⊓ {unopened folded
cells = 0}, and BCondG_R1 := B0R1′ ≤ V_G. `bat_ker_own_le_B0R1′` follows
from D34's `bat_ker_own_le_B0R1` and R1-2's `folded_unqueried_zero`. The
landed VerifierRelationsR1 statements remain true and are not edited. The
R1-3 worker was told before finishing PredicateR1. On the opened
coordinates BCondG_R1 held in all 506 evaluations (V_G = bat(ker own) =
dim B0R1′), and so did the fallback B0own ≤ V_G.

**D35.3 Duplicate parents (F4).** Queries sharing u/4 give identical line
relations. The relation rank is 8(4 + 22 + P), where P is the number of
distinct parents. dim B0R1′ is 952 generically and 616 or 568 on coset sets.
No statement may assume 47 independent relations.

**D35.4 C1Lift and H1Lift.** Measured on their own for the first time, both
held in every evaluation, including the adversarial consecutive and coset
sets:
- C1Lift on all 16 lanes: opened part 88/88, remaining 24/24;
- H1Lift: opened part 352/352, remaining 24/24.

So under D18 the opened part (D24.4 "not structural") was full on every set
tried. Under D29 these are conjuncts of P_R1, so no protocol change is
needed. A structural proof stays with Route P.

### Lead acceptance of R1-3, J2/J2-R1, J2b, J0, J13-R1 (2026-10-18); D36: clause (i′) on R1 has all its pieces

The worker commits are cherry-picked in dependency order:
- relations branch: 7e0b24607, f132a6b60, d26660a69, f628787e1;
- clause-(ii′) branch: 39b463f97, 7142d6be6.

The lead verified each host receipt (SHA matches the committed source,
exit 0, every axiom line standard, no sorry/axiom/admit/native_decide or
depth/heartbeat overrides):

| Module | Attempt | SHA | Axiom lines | Peak RSS |
|---|---|---|---|---|
| R1Z/PredicateR1 (D35.2-amended) | 3687 | `005130bb…` | 11 | — |
| R0Z/K4Values | 3686 | `1dd15cc5…` | 11 | 6.77 GB |
| R0Z/TerminalClosed | 3694 | `f41dc20a…` | 13 | — |
| R0Z/HonestValid | 3741 | `c73cb545…` | 37 | 6.79 GB |
| R1Z/NoiseLiftR1 | 3743 | `11f98af1…` | 14 | 6.78 GB |

PredicateR1 superseded 3684. NoiseLiftR1 was built against the amended
PredicateR1, and the SHAs match. The failed attempts (3685, 3740, 3742 and
others) were elaboration errors only.

**D36.1 Clause (i′) on R1 has every ingredient.**
- `chain0K4_le_silent_R1`: under P_R1, Chain0K4 lies in the silent image.
- `sRem_mem_chain0K4` (K4Values), for R0 and R1 together.
- `terminalClosed`: TerminalClosed is discharged from SemK4 ∧ PublicBase by
  per-family closure lemmas (Poseidon packed, schedule, occupancy, path,
  value, digest, asset, copy).

So sRem ∈ Chain0K4 holds unconditionally for base-typed honest instances
with α₉ ≠ ½. Only the one-line assembly `clause_i_R1` remains. BCondG_R1
uses B0R1′ (D35.2). The R1-3 version at 3684 is superseded and not used.

**D36.2 J0 (generic over Bat).** Proved: HonestValid, ValidOn, IIPrimeValid,
`HonestProver.restrict`, and `maskImageOn_restrict_of`. Also proved: the
corollaries showing that hvzk_on_of and the FsAbort theorems apply verbatim
to the restricted prover, the ι and inactive-sum lemmas for (R2)/(R3), and
the §1.4 obstruction as implications. One new fact: `inactive_1023`.

**D36.3 J13-R1.** `noise_lift_R1` gives the noise lift from P_R1's C1Lift and
H1Lift conjuncts. It projects by position (`hP.2.2.2.2.1`), so a reorder of
P_R1 must update it. It is proposed that P_R1 get named accessors.

**D36.4 J0b.** The route is proposed (ProductionHolds via LaneInterface, and
CopyLinkBalance pairwise cancellation). There is one decision first: u is
built from `applyEligible t 0`, which rebalances row 1023. J0b therefore needs
either a builder invariant (each semantic column of `h.build w` already sums
to zero over copyInactiveRows) or a lemma that row 1023 enters no production
lane or copy link. The lead's preference is the row-1023 lemma, because it is
a property of the fixed layout, not of the builder. To be settled by a short
source check before J0b is issued.

**D36.5 Remaining for MaskImageOn on R1:**
- `clause_i_R1` (assembly);
- J15-R1 (residual and mask lift for (ii′));
- J16-R1 (theorem and composition);
- J0b.

Outside Lean: the ZF1a/b couplings and their event bounds, ZF2, the Rust
P_R1 check with its refinement, and the D34.3 refinement items.

### Lead acceptance of clause (i′) on R1 (2026-10-18); D37

`R1Z/ClauseIR1.lean` (worker 8ba1c8b4f, cherry-picked) is accepted. Host
3695: exit 0, SHA `8eb17206…` matches, 2 standard axiom lines
(lead-verified).

`clause_i_R1_all`: under `P_R1 h.transport B hB ch`, with `PublicBase F x.1`
and `∀ w, h.public w = x.1 → BaseTyped F (h.build w)`, every
`sRem h B x w ch n` lies in `range (A ∘ inlM)`. This is the first conjunct of
`MaskImageOn P_R1` on R1. It has no transversality premise; P_R1 is the
prover-checked predicate (D29).

The remaining premises are typing facts about the statement and the honest
builder. `BaseTyped` for honest builds is a builder obligation of the same
kind as J0b. It joins J0b's scope: builder completeness, meaning honest
builds are base-typed and HonestValid.

Clause (ii′) (J15-R1, J16-R1) and J0b remain. The relations worker's lane is
complete.

### Lead acceptance of the R1-P design (2026-10-18); D38: the prover-side check

`z9/DESIGN-R1-P.txt` (worker 8a14c033c..19cb4c86b, cherry-picked) is
accepted as the plan. The prototype is `z4/z9b.rs --r1p`. Receipts:
`z9/runs/r1p-244d380ab/`. Expectations were committed before measuring.

**D38.1 The check uses public data only.** Every P_R1 conjunct is an exact
M31-limb rank or inclusion test built from fixed constants and the attempt's
challenges (α, z₀, z₁, γ, κ, α0, α1, queries). No witness, mask, salt or
seed enters.

BCondG_R1 reduces to one dimension test, because `V_G ≤ B0R1′` is already a
theorem (V_G_le, bat_ker_own_le_B0R1′). C1Lift and H1Lift rest on two
instance facts, `Vsem ≤ Wsem` and `Ph1 ≤ Wh1`, which are to be proved. They
are added to the open list.

**D38.2 Cost.** On the nuc (Core Ultra 7 155H, a laptop-class chip):
- 22.6 s and 130 MB per attempt on the actual query sets;
- 16 s on coset or {0..21} sets.

QPrime (12.5 s) and BCondG (9.3 s) dominate. P_R1 was true on every
configuration run. A laptop estimate is 20–30 s, unmeasured. Certificate
generation roughly doubles this. Code speedups of 5–20× are proposed but
unmeasured. Prover-latency impact: +20–50 s per proof at current code. This
is the cost of D29 and is reported to the user.

**D38.3 Prover integration (a plan for the spend-path branch, not applied).**
- The check goes in `prove_from_semantics` after the queries are drawn
  (prover.rs:229), before any proof byte exists, returning
  `Error::Rejected`.
- A capped loop around `prove_masked_attempt`, with N = 8 (accepted) and
  `AttemptsExhausted` publishing nothing.
- Fresh OS attempt secrets each time, with the nonce burned durably before
  use, and `private-leaf-salts` required.
- The fresh C1 root over fresh salts gives the fresh row-0 address that
  D31.2 requires.
- Rejected challenges and the failing conjunct are never logged persistently
  or remotely.

**D38.4 Lead decision: the proof account.** The nonce is bound to the
proof-account address, so each attempt uses a fresh proof-account keypair.
A rejected attempt's account is never created on chain, so this costs
nothing on chain. It is recorded as a prover requirement.

**D38.5 Refinement route: certificate checking (accepted).** Only soundness
of the check is needed: `check c = true → P_R1 rowEquiv B hB (decode c)`. A
false negative only costs an attempt, so degenerate cases fail closed. The
protocol's predicate is "the check passes", so by antitonicity of
MaskImageOn in P one lemma transfers `maskImageOn_R1`.

The Rust check emits preimage certificates, plus an echelon form with its
inverse for rank(relR1). A small checker uses only matrix-vector products.
The proof parts:
- the checker's semantics (generic linear algebra);
- the row formulas (the D34.3 refinement items, proved symbolically);
- an Aeneas extraction of the checker only.

The eliminating code itself is not extracted.

### Lead acceptance of J15-R1: clause (ii′) on R1 (2026-10-18); D39

The worker commits 298c1135c, 08f4b610f and 2acc2d919 are cherry-picked. The
lead verified each host receipt (SHA matches, exit 0, all axiom lines
standard, no sorry/axiom/admit/native_decide or overrides):

| Module | Attempt | SHA | Axiom lines | Notes |
|---|---|---|---|---|
| R0Z/IIPrimeResidual | 3747 | `f712e1d1…` | 22 | |
| R1Z/NoiseLiftR1 | 3748 | `cba81e30…` | 20 | supersedes 3743; adds named P_R1 accessors |
| R1Z/IIPrimeR1 | 3750 | `a9d99c89…` | 8 | |

Attempts 3744–3746 and 3749 were elaboration failures.

**D39.1 Clause (ii′) on R1 is proved.** `iiPrime_R1 : IIPrimeValid (P_R1
h.transport B hB) h B x`, given `PublicBase F x.1` and base-typed witnesses.
For two HonestValid witnesses with the same public statement, cTilde w −
cTilde w′ = A(inlM m + inrN n) for a mask tape m from the mask lift and a
noise tape n from the noise lift. Every challenge condition used comes from
P_R1, through its named accessors. The residual's batched cells lie in B0R1′
by `bat_L_mem_B0R1` and `folded_unqueried_zero`. Its round cells are
K₄-valued, using `terminalClosed`.

**D39.2 Row 1023 (D36.4) is settled by a layout lemma.**
`laneOf_actual_zero`: laneOf of the payload trace equals laneOf of `prepare
pub t ch`. It rests on `lanes_eligible` (TerminalEligible.lean:519) and on
every copy endpoint being Protected with row ≠ 1023
(HelperInvariant.lean:16–17). J0b therefore needs no builder invariant for
clause 1. It reduces to ProductionHolds on the prepared instance, plus the
helper sums of the same prepared trace.

**D39.3 Status of MaskImageOn on R1.** Both clauses are proved: (i′) by D37
`clause_i_R1_all`, and (ii′) by D39.1. What remains is J16-R1, the
assembly: `maskImageOn_restrict_of` with both clauses, then
`hvzk_on_restrict` and the FsAbort corollaries. Every step is an existing
lemma.

After J16-R1, the privacy theorem for R1 holds under:
- P_R1, enforced by the prover;
- PublicBase and BaseTyped;
- J0b (honest builds are HonestValid and BaseTyped);
- the ZF1 couplings and their event bounds;
- ZF2;
- the Rust check's certificate refinement (D38.5);
- the D34.3 row-formula items.

Memory: IIPrimeR1 peaks at ≈165 MB under -M7000.

### Lead acceptance of J16-R1 and J0b (2026-10-18); D40: the LogUp pole enters the privacy error

The worker commits 00ae72d55 and 53dd5023b are cherry-picked. The lead
verified both host receipts:
- R1Z/MaskImageR1: attempt 3751, SHA `45f65eda…`, 5 standard axiom lines;
- R0Z/HonestValidity: attempt 3752, SHA `a0214f63…`, 16 standard axiom lines.

Both exited 0, and neither file has sorry, axiom or overrides.

**D40.1 J16-R1.**
- `maskImageOn_R1 : MaskImageOn (P_R1 …) (validR1 h B hB x) B x`
- `hvzk_R1`
- `zkfs_R1_abort` and `zkfs_R1_abort_terms` (ZK_FS for the retrying
  restricted prover, error ε_hit + ε_coll + ε_prog, with the couplings as
  hypotheses).

Premises: PackField, PublicBase, and base-typed honest instances.
`validR1 = h.restrict (ValidOn P_R1 …)`.

**D40.2 J0b: proved conditionally, with an obstruction.**
`honestValid_of : HonestBuilderSound … → NoPole t λ χ → HonestValid`.
`HonestBuilderSound` has four named fields:
- baseTyped;
- lanes (ProductionHolds without Copy);
- helperSum;
- helperInactive.

The obstruction is `not_honestValid_of_pole`. At an active row where χ equals
a producer or consumer tuple value of the witness's own trace, the copy
residual is nonzero whatever the helper value, so HonestValid fails. NoPole
depends on the witness. It therefore cannot be a conjunct of the public
predicate P_R1, and the restricted prover `validR1` need not contain every
honest instance at every P_R1 challenge. As stated, the theorem would cover
fewer instances than the deployed prover runs on.

**D40.3 Lead decision: route (a), a statistical pole term.**
- Validity becomes per challenge (the instance set depends on ch), and the
  pole event is charged to the privacy error, not to P_R1.
- The honest prover behaves as the source does on an ActivePole (the
  attempt fails). It is treated as a retry whose trigger is
  witness-dependent. The effect of conditioning on that trigger is bounded
  by its probability, so it is charged as ε_pole and not hidden in P.
- Per attempt, for any fixed witness:

  Pr[¬NoPole] ≤ 4·|active rows| / |K_χ|,

  where χ = sem 1 is uniform in K₄ given λ, |K₄| = p⁴ ≈ 2^124, and there are
  at most 1,024 active rows. So the per-attempt bound is ≈ 2^-112.
- Over the cap N = 8: ε_pole ≤ 8·4,096/p⁴ ≈ 2^-109.
- This is the eprint 2023/245 situation handled correctly: a
  witness-dependent abort whose total probability is charged in full.

Lean work (J0c):
- HVZK_on with a per-challenge instance set;
- the FsAbort composition with an extra ε_pole term for a witness-dependent
  bad event (identical-until-bad);
- the pole mass bound from χ's uniformity (SemK4 sampler law);
- `maskImageOn_R1` restated on the per-challenge valid set.

**D40.4 Remaining builder facts.** These are carried as fields, not yet
proved:
- `helperInactive`: should follow from a registry fact, every copy endpoint
  on an active row, decidable over copyLinks as Protected was.
- `helperSum`: CopyLinkBalance plus a multiplicity or pairing registry fact.
- `lanes`: R0P builder completeness.

### Lead acceptance of the ZF1a/b coupling design and bounds for R1 (2026-10-18); D41

The ZF1 couplings work (worker 4f97292af..1e42b3685, 10 commits,
cherry-picked) is accepted. The design is `zf1/DESIGN-ZF1-COUPLINGS-R1.txt`
§1–§9. The lead verified the host receipts:

| Module | Attempt | SHA | Axiom lines |
|---|---|---|---|
| R0Z/FsAbortBounds | 3800 | `f5820c2f…` | 22 |
| R0Z/FsAbortR1 | 3802 | `617c7f3d…` | 11 |
| R0Z/FsAbortTape | 3806 | `80578d69…` | 3 |

All three exited 0. The axioms are standard, with `[propext]` alone on one
line. There are no overrides. Attempts 3801 and 3803–3805 failed (a numeral
limit and elaboration).

**D41.1 Proved.**
- Generic first-read and collision masses: `hit_le`, `pair_le`,
  `mass_cond_le`, `hitEv_mass_fresh` ≤ M·q/Umin, and
  `collEv_mass_fresh` ≤ M²/Umin.
- `realAbortCoupling_of_R1` and `idealAbortCoupling_of_R1`, which turn the
  R1 model into FsAbort's coupling hypotheses.
- `zkfs_R1_abort_N8`: ZK_FS ≤ 2^-166, for N = 8, q = 2^64, at most 2^21
  reads per attempt, and Umin = 2^255.
- `mean_decodeOrSpare`, the tape half of the real coupling.

**D41.2 Named hypotheses (fields of R1RealModel and R1IdealModel).**
- The lazy-programming law.
- The sampler's equal-fibre property.
- Game agreement outside the bad events (the Rust-to-Lean prover
  refinement).
- `HitFresh` and `PairFresh`, the designated-field table of §1.4.
- The read count: at most 2^21 per attempt, counted from source, not
  measured.
- The exhaustion mass.

**D41.3 Freshness.** These are assumed of the prover, and recorded as
requirements together with D29.3, D31.2 and D38.3:
- fresh OS secrets for every attempt;
- salted leaves;
- discarded attempts publish nothing;
- the attempt cap;
- the Rust check equals P_R1.

Given those, the chain "fresh salts → fresh C1 root → fresh row-0 address"
is proved, and each private read's hit or collision mass is ≤ 2^-255.

**D41.4 Numbers.** ε_hit 2^-167, ε_coll 2^-207 + 2^-476, ε_prog 2^-207.
Together with D40's ε_pole ≈ 2^-109, the pole term dominates the R1 privacy
error, at about 2^-109. QROM is not covered; classical ROM only.

**D41.5 Gaps recorded.**
- **G-root:** the Lean View has no commitment roots. Proposal: publish the
  roots, paths and opened salts as the verifier hash log at the front of
  `observerOracle`.
- **G-def:** R1's fs.real, fs.ideal and abort bridge are not defined in
  Lean. The spend-path LiteralByteProtocol is the model to mirror.
- **G-prog:** the lazy-programming law, together with G11.
- **G-ref:** the prover refinement, including the D34.3 items.
- **G-count:** an instrumented hash-call count.
- **G-exh:** the exhaustion count, in Lean.
- **G-retry:** the probe and the prover still lack the retry loop
  (D38.3).

Naming: the name `zkfs_R1_abort` now exists in both R0Z.FsAbortR1 and
R1Z.MaskImageR1. The final J0c statement must name one composite theorem
and cite both.

### Lead acceptance of J0c and `privacy_R1` (2026-10-18); D42: the R1 privacy theorem, conditional on named hypotheses

The worker commits a3c80b748, 4f903c387 and 376423b24 are cherry-picked. The
lead verified every host receipt (SHA matches, exit 0, axioms standard or a
subset, no sorry/axiom/admit/native_decide/overrides):

| Module | Attempt | SHA | Axiom lines | Peak RSS (KiB) |
|---|---|---|---|---|
| R0Z/HvzkV | 3754 | `9b8096b0…` | 21 | |
| R1Z/PoleMassR1 | 3760 | `b7ab6669…` | 11 | 7,202,756 |
| R1Z/ModelsVR1 | 3761 | `cfcf9954…` | 4 | |
| R1Z/MaskImageVR1 | 3762 | `179d2d98…` | 5 | |
| R1Z/PrivacyR1 | 3763 | `9be4fb32…` | 1 | |
| R0Z/HelperInactive | 3765 | `4424b826…` | 5 | |

Attempts 3755 and 3757 hit Lean's -M7000 memory exception. The work was
split into modules, and the failing sources were not rerun. PoleMassR1 peaks
about 137 MB under MemoryMax and must not grow; its Finset elaboration should
be reworked before the final replay.

**D42.1 `privacy_R1`.** It proves `ZK_FSV h (VR1 h) B outputs fs x ε` with

ε = M·q/Umin + (M²/Umin + εexh) + Mi²/Umin + N·4096/Q.

ZK_FSV quantifies over every witness w with h.public w = x.1. The real side
is the honest retrying prover. The simulator `simV` uses the per-challenge
pole-free set VR1. Hypotheses:
- PackField and PublicBase;
- `BuilderSoundOn`, the builder fields baseTyped, lanes, helperSum and
  helperInactive;
- `Sem1Uniform` for every adversary's draw;
- `R1RealModelV` and `R1IdealModelV`.

For N = 8, q = 2^64, M = 8·2^21, Umin = 2^255 and Q = p⁴, the value is
≈ 2^-109, dominated by the pole term. The Lean numeral for that
instantiation was dropped while working around the memory limit (D41's
r1_error_N8 covers the first three terms).

**D42.2 The V-form models (reviewed).** `ModelsVR1` keeps every D41 field
except agreement. Agreement now names the P ∧ no-pole games
(`middleRealAbortV`, `middleIdealAbortV`/`idealTestV`). This is required:
the honest prover accepts on P ∧ V, and the simulator retries on P alone.
The coupling bounds are re-proved as in D41. `hybrid_ideal_le` charges the
difference to `poleBad` (some attempt has P ∧ ¬V), whose mass is at most
N·4096/Q by `pole_mass_le` and the union bound. Accepted.

**D42.3 Sem1Uniform.** This is a new named premise, in upper-bound form: a
λ-indexed family of at most m values is hit by χ = sem 1 with mass at most
m/Q. No existing lemma fixes the FS draw's law (FsGood header; MaskD2's
`uniform_point_mass` is abstract). It joins the ZF1 refinement list, together
with the R1 sampler's correspondence (the spend-path sampler proofs are the
source).

**D42.4 Builder.** `helperInactive` is proved for every trace
(`active_registry`, [propext, Quot.sound]). Still open:
- `helperSum`: CopyRegistry's (row, slot) Nodup facts are the expected
  multiplicity input;
- `lanes`: R0P builder completeness.

**D42.5 R1 privacy status.** The privacy theorem for R1 now exists as one
Lean statement. It is conditional on:
1. P_R1, enforced by the prover through the D38 check (proving that check
   correct is the certificate route of D38.5);
2. the builder fields helperSum and lanes;
3. Sem1Uniform and the R1 real and ideal models: lazy programming, game
   agreement (prover refinement), the freshness tables HitFresh/PairFresh,
   and read counts;
4. the gaps G-root, G-def and G-retry (D41.5);
5. ZF2: `simV` and the choice-based simulator are not efficient;
6. classical ROM only.

No transversality premise remains (D29).

### Lead acceptance of J0d (2026-10-18); D43: helperSum proved; builder obligations reduced to three

The worker commits c2ff53224, 3388ce7c5, ba3fb2797 and 82e9e06e9 are
cherry-picked. The lead verified each host receipt (SHA matches, exit 0,
axioms standard or a subset, no overrides):

| Module | Attempt | SHA | Axiom lines | Peak RSS (KiB) |
|---|---|---|---|---|
| R0Z/HelperSum | 3871 | `8fc3d19f…` | 9 | |
| R0Z/BuilderSound | 3872 | `b6031988…` | 4 | |
| R1Z/PoleMassR1 | 3882 | `72fa96fc…` | 11 | 6,633,196 (was 7,202,756) |
| R1Z/PoleN8 | 3883 | `7eebeadd…` | 3 | 1,695,200 |

Evidence: `t2b2b/evidence-J0d.json`.

**D43.1 helperSum.** `helperSum_of_balance` proves that CopyLinkBalance on a
trace implies ∑ helper = 0 for all λ, χ. It uses CopyRegistry's
producer/consumer slot Nodup facts and keeps `helper`'s own 0⁻¹ = 0
convention. `HonestBuilderCore`, with fields baseTyped, lanes and balance,
gives `HonestBuilderSound` and `BuilderSoundOn` via
`builderSoundOn_of_core`. The builder obligations behind `privacy_R1` are
now exactly three:
- base typing;
- ProductionHolds without Copy;
- CopyLinkBalance of the honest build.

All three are R0P builder completeness.

**D43.2 PoleMassR1 reworked.** Only two proof bodies changed
(`poleSet_card_le`, `poleSet_card_le_4096`). The lead diffed every
declaration header: there are no statement changes. The module now adds
≈54 MB over its imports. Its dependent PrivacyR1 (source unchanged) must be
rebuilt in the final replay.

**D43.3 pole_N8.** `pole_N8_M31` proves 8·4096/p⁴ ≤ 2^-108 symbolically
(`m31_pow4: 2^123 ≤ (2^31−1)^4`). The combined numeric bound
(2^-166 + 2^-108) is not yet stated as one Lean term.

**D43.4 Process.** Attempt 3870 started just after another session's
charon/cargo job had launched, between the gate check and the launch. The
worker then moved the gate into the same SSH command as run2.sh, aborting on
a non-empty gate. That is accepted only as an aborting precondition. The gate
output must still be recorded per attempt.

### Lead acceptance of ZF2 (2026-10-18); D44: an explicit, witness-free simulator for R1

ZF2 (worker aca7598b5..749f9a778, 9 commits, cherry-picked) is accepted.
The design is `zf1/DESIGN-ZF2-SIMULATOR.txt`. The lead verified each host
receipt (SHA matches, exit 0, standard axioms, no sorry/axiom/admit/
native_decide/overrides, no `Classical.choose` in any of the sources):

| Module | Attempt | SHA | Axiom lines |
|---|---|---|---|
| R0Z/HvzkS | 3910 | `877fa7c7…` | 9 |
| R0Z/RefPayload | 3911 | `d7e378fd…` | 17 |
| R1Z/RefCosetR1 | 3912 | `deaffbc8…` | 2 |
| R1Z/SimulatorR1 | 3913 | `b2820559…` | 4 |

**D44.1 The simulator.** `simE π B outputs x ch t = (metadata outputs x
ch, shift x.1 B ch (refPayload x.1 B ch + A π B ch (equiv.symm t)))`. It
takes no instance and no InLanguage proof, and the lead read the definition.
`refPayload` is the zero payload trace's cTilde formula with S₀ added at
`.maskSum`, so it is computed from public data only.

The dummy-witness alternative was checked and rejected: such a view lies in
a different coset, at statistical distance 1, and the verifier's initial
sumcheck test already separates it.

Claim Z (`cTilde_sub_ref_mem_range_R1`): for every valid, base-typed w,
cTilde w − refPayload ∈ range A_ch.

**D44.2 `privacy_R1_eff`.** It proves ZK_FSS against simE with the same error
as `privacy_R1`. The hypotheses are unchanged except that the ideal model is
`R1IdealModelS … (simE …)`. This closes D42.5 item 5 (ZF2) at the level of
Lean statements.

Efficiency is a meta-level reading of the definition and is not formalised.
The axiom line's Classical.choice comes from propDecidable in `if`, not from
choice of a witness. Simulation cost equals the public P_R1 check (22.6 s
measured, D38) plus one payload computation (estimated, not timed).

**D44.3 New item G-sim.** A Rust simE with a host timing, a check that its
output passes the R1 verifier, and the L/O-split correspondence (with
G-ref).

Remaining for R1 privacy (D42.5, updated):
1. P_R1 enforcement: the D38 check and its certificate refinement.
2. Builder completeness: baseTyped, lanes, CopyLinkBalance (D43.1).
3. Sem1Uniform and the R1 real model plus R1IdealModelS, i.e. G-def,
   G-prog and G-ref (in progress).
4. G-root, G-retry, G-sim.
5. Classical ROM only.

### Lead acceptance of the R1 games (2026-10-18); D45: the ideal model is proved; real-side hypotheses narrowed

The R1 games work (worker 4d6ee9980..72f11706a, 12 commits, cherry-picked)
is accepted. The design is `zf1/DESIGN-R1-GAMES.txt` §0–§8. The lead verified
each host receipt (SHA matches, exit 0, standard axioms, no overrides):

| Module | Attempt | SHA | Axiom lines |
|---|---|---|---|
| R1Z/LensR1 | 3951 | `90bc5726…` | 10 |
| R1Z/TranscriptR1 | 3954 | `e8b6f22d…` | 18 |
| R1Z/GamesR1 | 3957 | `630393aa…` | 21 |
| R1Z/PrivacyGamesR1 | 3958 | `ec1a2ede…` | 2 |

**D45.1 The games are defined.** `fsR1` is the real and ideal pair, and
`abR1` is the abort bridge.
- The real game is the honest retrying prover: up to N attempts with
  independent secrets, accepting on P_R1 ∧ VR1 ∧ ¬exhausted. A rejected
  attempt publishes nothing; if every attempt fails, a fixed failure view is
  published.
- The ideal game is the same loop on P alone, with simE (or simV), answering
  from the table programmed at the published addresses.

**D45.2 G-root is closed at the model level.** It was checked against
verifier.rs and r1_semantic.rs. Every root, opened salt and path digest is in
the input or is the answer to a verifier read (115 transcript reads, plus one
leaf read and 6 node reads per query and tree). So proof = f(view, verifier
log), and `extend` puts that log at the front of observerOracle.

**D45.3 What is proved.**
- `R1IdealModelS` (simE) and `R1IdealModelV`, every field. The coupling is
  the identity, so Mi = 0 and ε_prog = 0. The programming collisions are
  charged inside the real side's M²/Umin.
- `R1RealModelV`:
  - the read count M = N·(115 + Mc), with `card_TRead = 115` proved;
  - transcript HitFresh;
  - PairFresh for transcript×transcript pairs and transcript×commitment
    pairs (the latter via `CmLayout.cross`).
- `privacy_R1_games` is privacy_R1_eff on the concrete games, with error
  N(115+Mc)·q/2^255 + (N(115+Mc))²/2^255 + εexh + N·4096/Q. The N = 8
  numeral is not compiled. It is expected to stay pole-dominated, ≈ 2^-108.

**D45.4 What remains a hypothesis.** These are fields of `R1RealData`, per
adversary and witness:
- `cp`: the lazy-programming coupling (G-prog);
- `Agree`: real and middle games agree outside the events (G-ref);
- `CmLayout`: hit, pair and cross for the salt, leaf, node, expander and
  seed reads;
- exhaustion mass ≤ εexh (G-exh);
- Mc: the commitment-read count, counted from Rust only.

These are also unchanged: Sem1Uniform, BuilderSoundOn (baseTyped, lanes,
CopyLinkBalance), PublicBase, and classical ROM only.

**D45.5 Rust ↔ Lean refinement list (design §6.4).**
- R-wire: framing, decoders, QueryScan, Merkle-path reads.
- R-ser: proof bytes = serialize(view, log).
- R-commit: prover.rs commitment phase and salted trees.
- R-causal: row i depends only on earlier challenges.
- R-retry: the retry loop in the Rust prover.
- R-pub: the Rust P_R1 check (D38.5 certificates).

**D45.6 Process.** The worker gated on Lean processes only, as instructed.
Spend-path cargo and charon jobs ran concurrently at times without incident.

### Lead acceptance of builder completeness (2026-10-19); D46: the builder is a refinement premise

Worker a46873ead..cf81ffd86, cherry-picked. `R0Z/BuilderComplete.lean`, host
4063 (in-window `run2-par.sh`): exit 0, 3.68 s, 6,616,004 KiB, 0 swaps.
SHA verified by the lead; standard axioms. Evidence:
`t2b2b/evidence-builder-complete.json`. Design:
`t2b2b/DESIGN-BUILDER-COMPLETE.txt`.

**D46.1 Inventory.** No concrete honest builder exists in Lean, here or on the
spend path.
- `HonestProver.build` is a field left deliberately uninstantiated
  (ZkStatement.lean:302–308).
- R0P and the spend path only extract from a trace: ProductionHolds,
  `lanes_zero_iff_holds`, CopyLinkBalance, `input_note_extracted`, and
  Rspend/extract.
- The builder exists only in Rust: the `compile_pool_v1_pair_forest_*`
  functions, then `host_semantic::build_with_material`.

**D46.2 Proved.**
- `lanes_iff_nonCopy`: for a base-typed trace and |K| > 4096, `lanes` is
  equivalent to `NonCopyHolds`, the seven families that read neither λ, χ nor
  column 26. The proof uses a pole-free χ obtained by counting.
- `baseTyped_ofColumns`: any `ofColumns` builder is base-typed by
  construction.
- `honestProverOf S Rel transport`.
- `builderSoundOn_of_refines`: BuilderRefines + |K| + PublicBase ⇒
  BuilderSoundOn.
- `inputNoteExtracted_of_refines`: a sanity check that the premise is the
  trace-side image of the payment relation that soundness extracts.

**D46.3 The premise.** `BuilderRefines S Rel` has two fields:
- `nonCopy`: NonCopyHolds of the honest build;
- `balance`: CopyLinkBalance of the honest build.

This is the builder's correctness against the Rust prover. It is a refinement
obligation of the same kind as the soundness side's source correspondence,
and nothing more follows from Rspend while the builder is abstract.

Ways to discharge it:
- a Lean model of the legacy builder (relocate_and_extend, the bank merge)
  with an Aeneas refinement of the Rust; or
- a per-build certificate the prover checks before publishing. Rust already
  checks the 18,089 transfer residuals at runtime (`finish`,
  pool_v1_pair_forest_honest.rs:80). A check-and-retry is witness-dependent,
  however, so as a privacy argument it would need a failure-mass bound like
  ε_pole. The lead's preference is the Lean model.

Instantiating W := Wspend and Rel := Rspend waits for the build integration.

### Lead acceptance of Sem1Uniform for R1 (2026-10-19); D47

The worker commits 36760a048, 9a9921af2 and eb4690a1b are cherry-picked.
Host attempts 4164, 4165 and 4166 ran in-window (slot 1). The lead verified
each (SHA matches, exit 0, standard axioms, no overrides). Attempts
4160–4163 were elaboration failures, each with a changed source. Evidence:
`zf1/sem1-uniform-evidence.json`.

**D47.1 Proved.**
- `sem1Uniform_abR1`: `Sem1Uniform ((abR1 W N hN).draw adv x) (p⁴ − 1)`
  for every adversary and statement, with no additive term.
- The exact form is `sem1_mass_le_exact` ≤ m·(⌊2^256/p⁴⌋+1)/2^256. The bias
  is multiplicative and ≈ 2^-132. Q = p⁴ − 1 is the best natural number.
- In abR1 the row-1 answer is its own uniform coin coordinate, so address
  repeats do not arise here. They stay charged to ε_coll in the real-to-middle
  coupling.
- `pole_N8_M31_pred`: 8·4096/(p⁴−1) ≤ 2^-108.
- `privacy_R1_games_sampler` is `privacy_R1_games` with `hdraw` discharged.
  Landed statements are unchanged.

**D47.2 Remaining premises (R-wire).**
- `SemRows01 W`: χ = sem 1 is `s1` of the row-1 answer, and sem 0 does not
  read it. This matches r1_wire.rs `begin`.
- `QM31SamplerLaw s1`: rank is a bijection onto Fin 2^256, emb is injective
  below p⁴, and s1 b = emb(rank b mod p⁴). It is restated from the spend
  path's proved sampler facts, which are pinned at 36353e178:
  - ExtractedQM31SamplerCorrect.sample_total;
  - qm31Digits_value;
  - SourceSamplerByteRank.rank;
  - sampled_decode_eq_iff.

The carrier transports (Array U8 32 ↔ Fin 32 → UInt8, and QM31 ↔ K) are the
open link. They join the build-integration job.

### Lead acceptance of G-prog/G-exh/G-count (2026-10-19); D48: commit interface corrected to phase-indexed roots

The worker commits 85307cedc and 30886c9d8 are cherry-picked. Host attempts
4002 (`R1Z/LazyTable`) and 4004 (`R1Z/CommitReadsR1`) ran in-window. The lead
verified both: SHA matches, exit 0, standard axioms. Evidence:
`zf1/r1-real-evidence.json`.

**D48.1 Proved.**
- Generic lazy programming: `mean_prog`, `prog_first`/`prog_off`, and
  `run_eq` (the middle game equals the programmed table on pairwise-distinct
  causal reads).
- Exhaustion: the M31 rejection loop rejects exactly 2 of 2^32 words, and
  εexh ≤ N/2^476 under `RCommitCount`.
- Read count: Mc = 1,685,214 + E₁ + E₂, and 115 + Mc ≤ 2^21.

Correction: the folded tree has 2^18 leaves, not 2^16 as the couplings
design said.

New R-commit premise `RCommitCount`: stream 1 has at most 45,056 limbs, which
assumes at most 26·1024 relation-free mask cells (to be confirmed from
aspis-statement); stream 2 has 4,096 limbs.

**D48.2 Modelling error found in the landed GamesR1.**
`R1Prover.commit` returns all three roots before the transcript. In Rust:
- the C2 root depends on rows 0–1, because its leaves include
  h1 = helper(λ, χ) (host_semantic.rs);
- the folded root depends on rows ≤ 29, since it is built over
  fold(q, α0) after α0 (prover.rs).

An R-commit premise equating `commit` with the Rust phase would therefore be
false, and `privacy_R1_games'` would be vacuous for the real prover. This
does not affect the landed theorems' truth: they hold for any `R1Prover`. It
affects only whether the Rust prover is an instance.

**D48.3 Lead decision: phase-indexed commitments.** Do not edit the landed
GamesR1. New modules define `R1ProverP`, with commit of type
`Challenges K → Fin 3 → OracleAnswer`:
- the C1 root is constant;
- the C2 root depends only on rows 0–1;
- the folded root depends only on rows ≤ 29.

These causality conditions are fields. Commitment reads and the exhaustion
flag are indexed the same way. `realAttempt.step` evaluates the roots at the
partial challenges, and R-causal covers them. The new games `fsR1P`/`abR1P`
reuse the ideal models and transcript freshness, which are unaffected because
the roots there are coins. Then `cp` follows from LazyTable with the
commitment reads in the causal read list, followed by CmLayout, Agree and
`privacy_R1_games'` on fsR1P.

The P_R1 check is unaffected: it reads challenges and public constants only,
not roots.

### Lead acceptance of the P_R1 certificate checker (2026-10-19); D49

The worker commits f38410320..80723cd38 (15) are cherry-picked. Design:
`zf1/DESIGN-P-CERT.txt` §0–§7. The lead verified both host receipts:
- `R1Z/CertSound`: attempt 4121, 20 standard axiom lines;
- `R1Z/CertR1`: attempt 4122, 7 standard axiom lines.

Both ran in-window, exited 0, have matching SHAs and no overrides. Attempt
4120 failed on missing imports.

**D49.1 Proved.** Generic certificate soundness:
- preimage certificates give the inclusions;
- the echelon certificate gives ker Rel ≤ span{n_f}, and hence the BCondG
  shape (no inverse of U needed);
- a right inverse gives the lift shape.

Each is decidable. At the exact P_R1 types: `qprime_of_cert`,
`bcondG_of_cert`, `c1lift_of_cert`, `h1lift_of_cert`, `halfOK_of_cert`,
`queryCard_of_cert` and `p_r1_of_cert`. These are relative to the
row-formula premises rf_own, rf_round, rf_bat, rf_src, rf_chain, rf_rel,
rf_obs and rf_dec, which subsume the D34.3 items.

**D49.2 Measured.** The Rust prototype `z4/z9c.rs` was run on the nuc in a
capped scope:
- A/J, actual or random queries: emit 11.9–12.6 s, check 2.56–2.65 s,
  14.2–14.4 MB certificate, 194–250 MB peak;
- coset: 9.2 s emit, 1.6 s check, 9.8 MB.

Emit plus check is about 15 s, which is cheaper than the 22.6 s eliminating
check. This replaces D38.2's "roughly doubled" estimate, so the prover-latency
cost of D29 is about 15 s per attempt with the current code. Ranks match
z9b, and 8/8 corrupted certificates were rejected at their intended steps.

On structure B the checker fails closed at the first C1 lift (rank
100 < 112), which is acceptable because a false negative only costs an
attempt. Whether C1Lift itself fails on B is not computed.

**D49.3 Enforced predicate.** P_chk := (emit succeeds ∧ check passes). It
transfers to `maskImageOn_R1` by antitonicity once `check_sound` is composed.

**D49.4 Open.**
- C2: the rf_* premises, including the Z4c round-coordinate map.
- C3: Aeneas extraction of the checker only. The constraints are u32/u64
  with proved bounds, flat Vec, plain while loops, monomorphic code, and one
  loop nest per function.
- `check_sound` composition.
- Prover integration, and timing on a second machine.

CertR1 peaks 0.27 GB under -M7000; wider importers must split. A Freivalds
check was rejected (§7.3).

### Lead acceptance of the builder model (2026-10-19); D50: Rspend strengthened by the change sentinel for privacy

The worker commits 23f5bd8cd..6d5a2889b (14) are cherry-picked. The design is
`t2b2b/DESIGN-BUILDER-MODEL.txt` §1–§7. The lead verified the six host
receipts:

| Module | Attempt |
|---|---|
| BuilderModel | 4201 |
| BuilderModelAux | 4204 |
| BuilderModelHash | 4208 |
| BuilderModelDigest | 4210 |
| BuilderModelSentinel | 4211 |
| BuilderModelBridge | 4212 |

All exited 0, ran in-window (slots 1 and 2), have matching SHAs and standard
axioms, and contain no overrides. The failed attempts were elaboration
errors, each followed by a changed source. Two whnf/simp timeouts were fixed
with local irreducibility; no limits were raised.

**D50.1 Proved.** `buildModel` is a staged Lean model of the Rust builder,
and all seven NonCopyHolds families hold for it (`nonCopy_model`):
- Poseidon holds by construction;
- schedule and path need no premise;
- value, occupancy, asset and digest hold under named witness premises.

**D50.2 Finding: no builder can satisfy `BuilderRefines S Rspend`.**
`refines_forces_sentinel` (lead-read): for any builder, BuilderRefines on a
private transfer forces `pub.change 7 ≠ 0`. Copy link 1124073492 places the
change digest on occupancy row 1018, whose sentinel equation requires it.
Rspend has no such clause, while the Rust builder already rejects a zero
sentinel with a salt retry (`two_outputs`).

**Lead decision.** The privacy relation is Rspend⁺ := Rspend ∧ (transfer →
change[7] ≠ 0). The soundness theorem continues to extract Rspend. This is
consistent, because the honest prover proves a subset of the relation that
soundness extracts.

On privacy, the salt retry conditions the change commitment (a public
statement value, a hash output in the ROM) on one limb being nonzero. That
affects the commitment's own hiding, which is outside this ZK theorem, by
at most the conditioning on a ≈2^-31 event, not the view given the
statement. This is recorded as an item for the note-commitment hiding
argument and is not checked here.

A soundness-side opportunity (not required): since accepted proofs force the
sentinel, the extracted relation could carry it too.

**D50.3 Modelling choices the Rust refinement must justify.**
- Block rows are defined by the canonical Poseidon transition. This moves the
  open raw-limb boundary to the builder side.
- Empty-root siblings come from the frozen table.
- Path aux levels are written from the node inputs.
- The model is total, with Rust's checks as premises.

**D50.4 Open, with the worker's estimates.**
- CopyLinkBalance of the model, 136 links: 3–5 days.
- BaseTyped of the model: about 1 day.
- Rspend⁺ → the model premises, after build integration: 2–3 days. This needs
  model digests equal to the spend path's noteCommitment, nodeCompress and
  pathPrefix.
- Aeneas refinement via extraction-friendly copies of each writer, checked
  by differential tests:
  - value, occupancy, path, merge: 2–3 days;
  - sponge and node: 2 days;
  - Poseidon: 1–2 weeks. This is the hardest item, and it has failed
    extraction before.

### Lead acceptance of builderRefines_model (2026-10-19); D51

The worker commits 69706d6bf..ffdc53471 (12) are cherry-picked. The lead
verified the nine green host receipts (attempts 4216, 4219, 4222–4225,
4228, 4229 and 4231): SHAs match, all exited 0 in-window, standard axioms,
no overrides. Evidence: `t2b2b/evidence-builder-model-2.json`. Design: §8 of
`t2b2b/DESIGN-BUILDER-MODEL.txt`.

**D51.1 Proved.**
- `buildModel_mem`, i.e. BaseTyped of the model.
- `balance_model`: CopyLinkBalance over all 136 links. It is generated by
  `copy-gen/gen_copy_links.py.txt`, which reads CopyConstants.lean, aborts on
  any kind mismatch, has a `--check` mode, and emits only named lemma
  applications. `decide` appears only on numeral bounds and row equations,
  and `rfl` only on weight literals.
- `builderRefines_model : BuilderRefines (buildModelSpec F) (ModelRel F)`.
- `builderSoundOn_model`, for characteristic 2^31−1.

So the builder premise of `privacy_R1` is a theorem about the model. What
remains is that the Rust builder refines the model, and the map from Rspend⁺
to ModelRel.

**D51.2 ModelRel** is what a later job derives from Rspend⁺ after build
integration. Its fields:
- pubBase and witBase;
- aux: conservation, pair-leaf validity, spendability, the D50 sentinel and
  the withdrawal amount;
- digest: anchor, nullifier, recipient, change, next root and carry, each
  equal to the model's digests;
- pairRight: the input pair's second commitment is the pair node's right
  child. This is the only new witness premise the links needed.

**D51.3 Violation.** Attempt 4218 re-sent 4217's source unchanged: the SHAs
are identical and it exited 1. A local edit script failed before launch.
This breaks the never-rerun-unchanged rule. It is recorded in the evidence,
and the worker's launcher now refuses a source hash it has already sent.
That guard is adopted for all workers.

### Lead acceptance of the phase-indexed real games (2026-10-19); D52: privacy_R1_games′

The worker commits 142b9fa15..99b6f9149 (17) are cherry-picked; GamesR1 is
untouched. The design is `zf1/DESIGN-R1-REAL.txt` §1–§7. The lead verified
all 15 green host receipts (4007 … 4049): SHAs match, all exited 0
in-window, standard axioms, no overrides. Notes on the failed attempts:
- 4005 is void: another worker's leftover launcher in the shared scratchpad
  ran, compiled nothing, and the worker switched to a private launcher.
- 4033 hit the default heartbeat limit and was fixed by restructuring, not by
  an override.

**D52.1 Proved.**
- `R1ProverP` with phase-indexed roots (D48.3). Each attempt is one causal
  read program run on partial answer vectors.
- cp: the frozen-set lazy-programming law (`LazyFrozen`), with
  H(public_bytes) as the frozen address, and `cpP`.
- CmLayout: the byte grammar `gram` for every commitment read, and hit,
  pair and cross freshness for all N·|Pos1| positions. `hidden` shows the
  opening log does not move on unopened reads.
- Agree: `agreeP`.
- exh: εexh = N·16(L₁+L₂)/2^496 + N·|Pos1|/2^255.
- `privacy_R1_games′` on fsR1P/abR1P against simE. The error is
  M·q/2^255 + M²/2^255 + εexh + N·4096/(p⁴−1), with M = N·|Pos1|.

Every field of R1RealData is discharged.

**D52.2 Hypotheses of privacy_R1_games′.**
- PackField, PublicBase, BuilderSoundOn (theorem for the model, D51),
  SemRows01 and QM31SamplerLaw.
- R-rom: `RomModel W`, `RAddrIn`.
- R-causal: `RCausal`.
- R-commit:
  - `RCommitBytes` (the node, leaf, salt, seed, binding and expander
    grammars);
  - `hfib`;
  - `RExh`;
  - E bounds, and 16L ≤ 8E.
- R-wire: `eCm`, `ROpen`, `RComLog`.

Every one of these is a statement about the Rust prover's behaviour, which
is what the refinement work discharges.

**D52.3 Modelling choices (reviewed).**
- The mask nonce is secret. It is never in the proof bytes or read by the
  verifier, per r1_wire.rs, which overrides the "public" context comment.
- The binding read is memoized: the Rust recomputes it at the same address.
- The real game runs all N attempts and charges every read. That is
  conservative.
- The cell bound ≤ 26·1024 (RCommitCount) still needs confirming from
  aspis-statement.

**D52.4 Open.**
- R-ser, R-retry, R-pub.
- Completeness of the read list, i.e. no other hash call in the commitment
  phase.
- The Rust-side discharge of every premise in D52.2.
- An LE byte-formula lemma for `wordsE`.
- The N = 8 numeral.

### Lead acceptance of the rf_* premises (2026-10-19); D53: P_R1 from the checker's tests

The worker commits e899fcdd6..c61320358 are cherry-picked. The lead verified
the 12 green host receipts (4281, 4282, 4287, 4289, 4290, 4294, 4296, 4297,
4299, 4300, 4302 and 4303): SHAs match, all exited 0 in-window, standard
axioms, no overrides. Evidence: `zf1/rf-evidence.json`, 24 attempts. The
failures were memory and recursion blowups and naming errors; none was rerun
unchanged and no cap was raised. 4296 had finished green before the
session-limit cut, and was recorded without a relaunch.

**D53.1 Proved.** On the Lean side, all eight rf_* premises are discharged:
- RF-dec: the decode8 limb order;
- RF-src: Rust-built sources lie in Gonly, Vsem and Ph1;
- RF-chain: ChainT0K4 lies in the span of the Rust chain_targets under SemK4;
- RF-round;
- RF-own: ownMap equals the Rust raw_c columns, with the 12-lane limb
  layout;
- RF-obs/RF-col;
- RF-bat/RF-rel: the wflat order, and B0R1′ ≤ ιb(ker Rel).

D34.3 items 1 and 2 are proved on the Lean side: `storedFirstLineX18` =
the Rust line_node formula; lineInverse = the QueryGeometry multipliers; and
line_fold_with_inverses = lineFoldLinear.

`p_r1_of_checks` derives P_R1 from the checker's tests (PreOK, PreOK₂,
EchOK, RinvOK, half-inverse, limb/length). Its remaining hypotheses are not
row formulas:
- the circle points lie in K₄;
- wb is an F-basis of K;
- the opened folded-cell list covers the open cells;
- one-index side conditions on the selected lift sources.

**D53.2 Moved to C3 (Rust side).**
- The round, batched and relation matrices, and some own columns, are
  defined as the Lean maps' coordinates. C3 must show the Rust builders
  round_row/tail_row, unit_functionals and design_relations/
  limb_functionals compute them. The other columns already have Lean closed
  forms matching the Rust.
- D34.3 item 3 (`ell` versus Rust weight kinds 5/6).
- π versus the Rust transport table, `natural` versus naturalLineValue, the
  stored points, and batch inversion.
- check_sound, i.e. extracting the checker and composing it with
  p_r1_of_checks.

### Lead acceptance of the first builder refinement (2026-10-19); D54

The worker commits 8288078b9..6a655b053 (13) are cherry-picked. The lead
verified the 11 green host receipts (4233, 4235, 4238, 4241, 4246, 4248,
4253, 4257, 4258, 4260 and 4262): SHAs match, all exited 0 in-window,
standard axioms, no overrides. Attempt 4237 (exit 1) was checked after the
session-limit cut, and nothing was resent unchanged. Design:
`t2b2b/DESIGN-BUILDER-MODEL.txt` §9.

**D54.1 Proved, for the value, occupancy, path-aux and merge writers.**
- Extraction-friendly Rust copies are in `refine/writers`.
- Native differential tests against production (read-only from the spend
  branch at 0c46bf447): 200k value, 100k occupancy, 52k path and 1M
  node_right cases; 2k merge shape violations; the 2 saved fixtures; and 256
  randomized full honest compiles.
- Extraction with pinned Charon cb50ff16 and Aeneas b59d5188.
- In Lean:
  - `aux_block_model`: write_aux_block equals model block 63;
  - `path_block_model`: rows 912..1007;
  - `merge_model`.

Loops are handled by induction; nothing is evaluated.

**D54.2 Lead rulings.**
- **B1 accepted.** `import Aeneas` is replaced by `import Aeneas.Std` and
  `import Aeneas.Tactic.RustAttributes` in the generated file, and the edit
  is asserted by `refine/extract/substitute.py.txt`. The full `Aeneas` root
  does not build unpatched under 4.32 in this tree. Build integration must
  reconcile this Aeneas.Std with the spend path's ported one: two versions
  cannot coexist in one tree.
- **B2 accepted.** The generated `maxHeartbeats`/`maxRecDepth` lines are
  deleted, which is stricter than generated, and the code compiles without
  them.

**D54.3 Open.**
- `node_right_lane7` and the path read-back are checked by differential test
  only.
- ValueLifts, OccLifts and PathLifts are premises. They need the
  Wspend-to-Rust-witness map and the Poseidon/node refinement.
- The merge is proved against an abstract table.
- The copy-to-production link is a differential test, not a proof. The
  production writers use Vec, closures and M31 methods the pinned extractor
  does not handle. The options are a production-source migration (as with
  Decision 1 on the verifier) or accepting tested equivalence.

### Lead acceptance of the sponge/node refinement (2026-10-19); D55

The worker commits d66998036..efd49c19f (9) are cherry-picked. The lead
verified the 7 green host receipts (4263, 4266, 4268, 4271, 4272, 4275 and
4277): SHAs match, all exited 0 in-window, standard axioms, no overrides.
Design: §10 of `t2b2b/DESIGN-BUILDER-MODEL.txt`.

**D55.1 Proved.** The Poseidon permutation is kept abstract through the
plug-in premise `RoundsOk rounds B`: the eleven odd-round outputs lift to the
model's block iterates.
- `block_model`: write_block equals blockCell.
- `node_model`: write_node equals the model's nodeIn block.
- `m31_add_spec`/`m31_sub_spec_wide`, for all canonical inputs.
- `sponge_model`: the full sponge, given the initial state, the absorptions,
  chaining and RoundsOk.
- `note_sponge_model`: the note blocks 1–3, 27–29 and 30–32.

B3 is closed in Lean:
- `node_right_lane7_lift`: the large tweak.
- `read_back_node`: at the copy level. The production relocation still
  links to the copy by differential test.

Differential tests against production were run with `rounds` from the
production permutation:
- 1M M31 add/sub pairs;
- 20k write_permutation, 20k node/forest-node and 20k sponge cases;
- 3,648 full blocks.

**D55.2 Open.**
- Instantiating the owner and nullifier sponges and the tree/append node
  blocks. These are mechanical, by the same pattern.
- `RoundsOk` for the Rust permutation: the Poseidon job.
- The input lifts (Wspend → Rust witness).
- The copy-to-production link (D54.3).

### Lead acceptance of the block assembly and the Poseidon round lemmas (2026-10-19); D56

The worker commits after 1b56fef13 are cherry-picked. The lead verified the
green host receipts (4400, 4401, 4404, 4406 and 4407): SHAs match, all
exited 0 in-window, standard axioms, no overrides. Attempts 4402, 4403 and
4405 were local elaboration fixes. Design: §11 of
`t2b2b/DESIGN-BUILDER-MODEL.txt`.

**D56.1 Proved.**
- `builder_blocks_model`: all 57 Rust-written blocks equal buildModel, under
  RoundsOk, the input lifts and the copy↔production links. Discharge lemmas
  cover chaining, absorptions, node children and digests. RoundsOk is the
  only Poseidon obligation left for the block region.
- `full_round_lift`: an extracted full round equals R0P
  `poseidonFullRound` for every u32 state. No canonicity hypothesis is
  needed: the u64 reductions mod p never overflow.
- `internal_round_lift`: the same for an internal round, matched to R0P's
  ordered foldl through a general ofFn/range′ lemma.
- `PoseidonTables`: INTERNAL_SHIFTS satisfies ShiftsBound/ShiftsOk with
  small numerals only.

Differential tests (diff-g):
- perm_rounds equals the production odd-round outputs on 100k states and on
  all 1,824 blocks of 32 traces;
- the final state equals production `permute` on 50k states;
- m31 add/mul agree on 1M pairs.

The extraction needed no adapter. This is the first time Poseidon has
extracted and its rounds have been proved; the spend path's earlier attempts
stopped at the external wrapper and round composition.

**D56.2 Remaining for RoundsOk.**
1. Generated per-row constant-lift lemmas for EXTERNAL_INITIAL/FINAL and
   INTERNAL, going through `Nat.cast_ofNat` without unfolding large literals.
2. `apply_round_lift` and `leading_pair_lift`.
3. A `perm_rounds` loop invariant, giving RoundsOk for the copy's output.

The copy↔production link stays a differential test (D54.3).

### Lead acceptance of C3: the extracted P_R1 checker (2026-10-19); D57

The worker commits 54f39d467..4f5496ea4 are cherry-picked. The consistent
chain is CertCheckExtracted (4345), then 4363–4373: CertCheckBase … Top,
CertData/2, CertCheckData, CertCheckSound and CertCheckSoundAll. These are
dependency replays: Base and Dot had originally been built against the 4341
extraction. The lead verified all eleven (SHAs match, exit 0, standard
axioms) and checked that no source contains sorry, admit, native_decide or
an override. The replays used the global lock, the caps were not raised,
and CertCheckSoundAll peaked at 7.15 GB, near the cap. The launcher now tags
deliberate dependency replays (`DEPREPLAY=1`).

**D57.1 Proved.** `check_sound`: if the extracted Rust `check pb c` returns
`ok true`, then P_R1 holds on the decoded record. The Rust checker in
`c3/check`:
- is no_std, monomorphic, with checked u32/u64 arithmetic, one loop per
  function and branch-free bodies;
- verifies every certificate-supplied intermediate by plain equality.

Differential test: same verdicts as z9c on the five configurations and the
8 corruptions, and 6/6 corruptions of the new fields rejected. It takes about
8.8 s per check, so the prover-side check is now ≈ 12.6 s emit + 8.8 s check
per attempt, before optimisation.

**D57.2 Hypotheses of check_sound.**
- The builder identifications hOwn, hRound, hChain, hRel, hGOwn, hGRound,
  hGBat, hC1 and hH1. These carry the D53.2 items: `ell` against weight kinds
  5/6, π against the transport table, `natural`, the stored points and batch
  inversion.
- Decoder facts: hhalf, hup, hnq, hz, the lane layouts stO/stG, and φ.
- From p_r1_of_checks: wb, hcov, hsel1/hselH.

The checker reads values mod P, so it also accepts non-canonical
certificates. That is sound, but the differential test does not cover it.

**D57.3 Next.** Extract the column builders (raw_c, round_row/tail_row,
unit_functionals, design_relations/limb_functionals, normalize_d) to
discharge the builder identifications, and integrate the checker into the R1
prover (D38.3).

### Lead acceptance of RoundsOk for the Poseidon copy (2026-10-19); D58

The worker commits dc98360df, 928e057e2, 0bac06653 and f1ef3e481 are
cherry-picked. The lead verified host attempts 4408, 4409 and 4410 (SHAs
match, exit 0 in-window, standard axioms). No source contains sorry, admit,
native_decide, an override, decide or norm_num.

**D58.1 Proved.**
- `PoseidonConstLift`, generated. The generator reads production
  poseidon2.rs, the copy, the extracted Lean and R0P PoseidonConstants.lean,
  and aborts on any disagreement. Its tamper test is recorded: two injected
  value changes aborted with exit 2, and a tampered output failed --check
  with exit 1. All 142 lanes are proved by named steps; no large literal is
  unfolded.
- `apply_round_lift` (all 22 rounds) and `leading_pair_lift`.
- `perm_rounds_lift`, by loop invariant: RoundsOk holds for the copy's
  permutation.
- `builder_blocks_model_copy`: under `BuilderInputLifts`, the old lifts
  without RoundsOk, all 57 Rust-copy blocks equal buildModel.

**The Poseidon obligation of the builder is closed for the copy.** The
copy↔production link is the diff-g differential test (100k states and 1,824
compiled blocks), with the same standing as the other writers (D54.3).

**D58.2 Remaining builder items.**
- Sponge pre-state chaining, which is short with RoundsOk now proved.
- Linking BuilderInputLifts to the witness-level writer outputs, and the map
  from Wspend⁺ to the Rust witness.
- The copy↔production decision (D54.3): migrate the production prover
  writers to the extracted copies, or accept tested equivalence. To be put
  to the user.

### Lead acceptance of the first column builder (2026-10-19); D59

The worker commits 2660e7a5f..c681d4634 are cherry-picked. The lead verified
the 8 green host receipts (4374, 4376, 4377, 4378, 4381, 4385, 4388 and
4391): SHAs match, exit 0, standard axioms, no overrides. The 10 failed
attempts all had changed sources.

**D59.1 Proved.** The chain-target builder `fill_tq` has an extracted Rust
copy. Its differential test matches z9c's chain_targets on all 1,175,056
entries in each of five configurations, and the checker verdicts are
unchanged. On the Lean side:
- the QM31 layer (CertBuildBase/Tower) shows the extracted QM31 product is
  the product in K, under the premise `Tower B` (i² = −1, u² = 2 + i);
- `chain_ident` shows the builder output under φ equals Lean's chainTarget.

`check_sound′` removes hChain and hhalf. In their place it adds:
- hT, the tower premise;
- hal and ha9, saying the Rust alpha limbs are the raw challenge limbs;
- hbuild, saying the prover filled the target matrix with the extracted
  builder.

CertCheckSound2 peaks at 7.16 GB, near the cap.

**D59.2 Remaining builder identifications.**
- hOwn, hGOwn, hC1, hH1 and hRel (raw_c, design_relations). These need
  copies of eq/points/h_weight/evalrow, `natural` = naturalLineValue, the
  stored points, π against the transport table, inactive against
  copyInactiveRows, and the flatC1/flatO layouts.
- hRound, hGRound and hGBat (round_row/tail_row, unit_functionals). These
  need closed forms for the pure-round coordinates, plus `ell` against weight
  kinds 5/6.

Lead ruling: π, the stored points and the OOD points may be taken as input
arrays under named premises (for example "the input table equals π"), to be
discharged with the transport and sampler refinement.

Housekeeping: the builder extraction reused two host output directories from
the superseded first checker extraction. That is recorded; the accepted
chain does not reference them.

### Lead acceptance of the witness-level Rust-copy builder (2026-10-19); D60

The worker commits 8e3e1e172..f027039ef are cherry-picked. The lead verified
host attempts 4412, 4413, 4415, 4417 and 4419 (SHAs match, exit 0 in-window,
standard axioms). Attempts 4411, 4414, 4416 and 4418 were local fixes.
Design: §12.

**D60.1 Proved.**
- `builder_blocks_model_chain`: sponge pre-states are computed, from
  sponge_init and row 10 of the previous block's perm_rounds.
- `PoseidonCanon`: perm_rounds outputs are canonical.
- `builder_witness_model`: for u32 witness and public records (`RustWitness`,
  `RustPublic`) with the named map `toModel` and premise sets `PubCorr` and
  `WitnessOk`, every extracted component returns ok, and every cell of the
  composed 29×1024 trace lifts to `buildModel pub (toModel W)`.

PathLifts, ValueLifts and both OccLifts are now theorems. `invR` rests on
the named premise `Nat.Prime 2147483647`. It is proved elsewhere in the repo
(AspisV8R15.ExactTowerBase) and joins the build-integration list.

**D60.2 Open.**
- The Lean glue (block order, chunk words, child order, invR, assembly)
  matches pair_trace.rs by inspection only. It needs a differential test.
- The stable/late bank merge is not in the composition yet.
- The Wspend⁺ → RustWitness/ModelWitness map (§12.6): values (transfer vs
  withdrawal), keys and salts, path bits and siblings at levels 0, 1–20 and
  21–23, the public side, the WitnessOk/PubCorr range facts, and the
  primality import.
- The copy↔production link (D54.3).

### Lead acceptance of the merged builder, M31 primality and the glue test (2026-10-19); D61

The worker commits 6cf89c077..106f12df5 are cherry-picked. The lead verified
host attempts 4421 (`M31Prime`) and 4426 (`BuilderWitnessMerged`): SHAs
match, exit 0 in-window, standard axioms. Attempts 4420 and 4422–4425 were
local fixes. Design: §13.

**D61.1 Proved.**
- `m31_prime`, by a Lucas certificate with witness 7 over the factorisation
  of p−1. It uses reduce_mod_char modular powers with no value above p², one
  literal-comparison `decide` per check, and norm_num only on the seven small
  primes.
- `builder_witness_merged`: with the late bank on rows 544–863 and the stable
  bank elsewhere, merge_check returns true, merge returns ok, and every cell
  equals `buildModel pub (toModel W)`. The only premises are PubCorr and
  WitnessOk.

**D61.2 Glue differential test.** Production rejected none of the
inputs. The copy's merged trace equals the production forest compile cell for
cell in columns 0–15, on:
- both saved fixtures;
- 512 randomized honest witnesses.

Columns 16–28 are the model's zero stage-H columns and are not compared.
Each of seven single-field mutations makes 1 to 9,788 cells differ, which
shows the comparison has teeth. The Lean glue and its Rust mirror are
generated from one table (`refine/glue/gen-glue.py.txt`). Its `--check`
requires verbatim Lean text in the proved files, and it rejected two
deliberate edits. The structural functions are mirrored one-to-one and are
covered by the full-trace comparison.

**D61.3 Builder status.** The honest builder, as composed extracted Rust
copies, is proved to produce the model's trace, the model satisfies the
builder premise of `privacy_R1` (D51), and the composition is differentially
equal to production. Remaining:
- the Lean-side Wspend⁺ → RustWitness/RustPublic map (§12.6), after build
  integration. The Rust side of the map is `records` in glue.rs.
- the copy↔production decision (D54.3).

### Lead acceptance of the lift-column builder (2026-10-19); D62

The worker commits a88b52d9e..830d9e275 are cherry-picked. The consistent
chain after re-extraction is:

4392 → 4393 → 4394 → 4395 → 4398 → 4399 → 4460 → 4461 → 4463 → 4464 →
4466 → 4470 → 4473 → 4474 → 4478 → 4479 → 4480

The lead verified all 17 (SHAs match, exit 0 in-window, standard axioms, no
sorry/admit/native_decide/overrides). Eleven failed attempts all had changed
sources.

**D62.1 Proved.** `fill_lo` (C1 and H1 lifts) has an extracted Rust copy.
Its differential test matches z9c's lift matrices on all 342,080 entries in
each of five configurations. On the Lean side:
- the helper values in K (eq, the successor/xor-12 points, h_weight, the
  natural basis, evalrow);
- `natR_eq`: Rust `natural` = naturalLineValue. This is a real lemma, and it
  closes that D53.2 item.
- `c1_entry_ident`/`h1_entry_ident`: every entry is the flatC1/flatH1
  coordinate of `obs`.
- `check_sound″`: hC1 and hH1 are removed.

D59's `check_sound′` had a duplicated binder; it was harmless and is removed
in 4479.

**D62.2 New premises under the D59.2 ruling.**
- htr (input table = π), hzx/hzy (OOD points), hsx/hsy (stored points), hin
  (Rust inactive flags = copyInactiveRows). hin is accepted as a named input
  premise, of the same kind as π.
- hselC/hselHv, hloC/hloH (layout), and hblo (`pb.lo` filled by `fill_lo`).

CertCheckSound3 peaks at 7.17 GB.

**D62.3 Remaining in check_sound″.**
- hOwn and hGOwn: the own-matrix builder and the blockM layout.
- hRel: design_relations/limb_functionals.
- hRound, hGRound and hGBat: pure-round closed forms, and `ell` against
  weight kinds 5/6.
- The decoder facts and the inherited premises.

### Build-integration design and a coherence finding (2026-10-19); D63

The worker on side branch `codex/r1-privacy-build-integration-20261019`
(commit ee17c8c86, based on the 100-bit branch with v8-reference merged)
produced `t2b2b/DESIGN-BUILD-INTEGRATION.txt` and compiled host attempts
4520–4529. The branch is pushed by the lead.

**D63.1 Coherence finding (lead-verified).** Neither host workspace is a
single coherent build.
- Lean loads one object per module name and does not check it against what
  dependents were compiled with.
- The privacy and spend closures share module names with different objects:
  the sampler closures share 28 names, 23 with different objects and 6 with
  different sources.
- The spend side itself has more than one object for `CircleGroupOrder`.
- In privacy objects2, `R0P/CoreExt` was re-sourced and recompiled on
  2026-10-08 09:24, while its dependent `R0P/Copy` dates from 2026-10-07
  18:36 and was never rebuilt.

Consequence: every focused compile accepted so far, on both tracks, is
evidence that each module checks against the objects present. None is yet
evidence of one consistent theory. No accepted statement is withdrawn. But
**nothing is release evidence until one clean ordered build, from one source
per module name, on one base, with one axioms audit.** That is also the
outstanding "single Lean 4.32 kernel" item on the soundness side.

**D63.2 Lead decisions.**
- Adopt the design's target: a new workspace with one sources tree, one
  objects folder, Mathlib from AspisFormal, and the spend path's ported Aeneas.
  The build compiles in dependency order from a manifest with `--check`. Where
  the two sides' sources differ, take the spend copy and repair privacy
  imports.
- New item (f), the unified base, comes before (b), (d) and (e). The
  provisional soundness release roots are:
  - LiteralFreshAttemptBound, RawAdaptiveMembershipBound,
    AdaptiveMembershipSoundness;
  - SpendRelation, SpendAppendBinding;
  - the terminal/caller correspondence modules the live session lands.

  These are to be confirmed with the soundness side at final assembly.
- SemRows01 moves to (d), as a wire-decoder fact.
- On (e): the worker reads `line_identity` as the honest-data form of
  `match1`, not as an assumption of R1QueryResidualBridge. This is to be
  settled when the soundness side states which premise it would discharge.
- Attempt range for the integration build: 5000–5299, using the private
  joint launcher (same caps, slots and run2.py; only the objects folder and
  search path change). The build spans several night windows.

**D63.3 Done (on the side branch).**
- BatchedAlgebra and its dependents compile against the spend path's own
  `R1FoldCoefficientBridge`/`R1FirstFold` (byte-identical), with 0 coherence
  conflicts over 266 modules. So `line_identity` is stated over spend
  constants.
- `qm31SamplerLaw_spend` is proved on the spend base from the extracted
  `qm31_sample`, with the carrier transports, and `SamplerLawBridge.toSem1`
  is proved. They sit on different bases until (f).

### Lead acceptance of the own-column builder (2026-10-19); D64

The worker commits 0a3d14c9e..a1c258b5e are cherry-picked. The consistent
chain is 4481–4499 and 4510–4512 (`builders[2].consistent_chain` in
c3-evidence.json); the lead verified the new modules. Attempt 4501 hit -M7000
at 7.17 GB, and the worker split the module rather than raising the cap.

**D64.1 Proved.** `fill_own` has an extracted Rust copy, and its
differential test equals z9c on all five configurations:
- the QPrime own matrix: 2,952 sources, 1.11M entries;
- the G own matrix: 1,980 sources, 744k entries.

On the Lean side: `obs_lane`, `own_c1_ident`/`own_h1_ident`,
`own_src_ident` (the blockM/flatO layout), and `check_sound‴`, which removes
hOwn and hGOwn. The QPrime sources are now defined from the Rust descriptors
(`srcOf`), not assumed. The new premises are the builder runs and the
descriptor, width, layout and stride facts.

**D64.2 Remaining in check_sound‴.**
- hRel: needs a WideExact (8-limb) tower premise, the relR1 relations, and
  copies of design_relations/limb_functionals. It is a multi-session job.
- hRound, hGRound and hGBat.
- The decoder facts.
- The named input premises.

Memory: CertCheckSound4 peaks at 7.19 GB. Further composition must happen
at the CertData level, with no Aeneas import in the composing module.

All of this is subject to D63: release evidence requires the unified build.

### Unified-base build of the privacy closure (2026-10-19); D65: the R1 privacy theorems check in one coherent build

Side branch `codex/r1-privacy-build-integration-20261019` (dbfe84f12, pushed)
holds manifest 1: the closure of the privacy roots, 402 modules (8 spend, 237
base, 157 privacy). It was built from one repo revision (v8-reference
66bca8914 plus spend f05b0e63e) in the new host workspace
`aspis-joint-20261019`: one sources tree, one objects folder, AspisFormal
Mathlib and the Aeneas 4.32 port. The build ran in dependency order, one
module at a time, as attempts 5000–5402 (03:38–04:02 London), with 0 swaps
and peak 7.18 GB.

Where repo sources differed, the spend copy was used:
- the six narrowed base files;
- `V6PublishedTheoremInterfaces`, `R0P.LogUpChain`, `R0P.LogUpAssembly` and
  `R0P.SemRounds`.

**Lead verification.** All 403 host logs were parsed, including wrapped axiom
lists. The only axiom sets are subsets of {propext, Classical.choice,
Quot.sound}: 2,437 + 340 + 90 + 6 reports. The single `sorryAx` is in the
failed attempt 5068, which the error produced. The only non-zero exit is
5068: `AspisV8R19.R443BoundedRejectionMass` used `field_simp` without
importing it, and the old base supplied it through all of Mathlib. The fix
adds `import Mathlib.Tactic.FieldSimp`, an import-only change to the base
tree `v8-full-view-zk-20260912`. The lead accepts it; it must also reach
v8-reference's copy. It recompiled green at 5069.

The root theorems check with standard axioms only, in one coherent theory:
- `builder_witness_merged` (5283);
- `check_sound″` (5387);
- `privacy_R1_games` (5398);
- `privacy_R1_games_sampler` (5401);
- `privacy_R1_games′` (5402).

Object hashes are in `t2b2b/build-integration/joint-objects-manifest1.sha256`.
This settles D63 for the privacy closure. The soundness roots remain.

**Open (D63.2).**
- The soundness roots wait on soundness-side hygiene: three missing sources,
  the X/R1X double imports of SpendRelation/SpendAppendBinding/TraceAppend,
  and three name collisions.
- (c) end to end: the spend sampler stack in this workspace.
- (b), (d) (Rspend⁺ map, SemRows01) and (e).

### Lead acceptance at the 2026-10-19 cleanup: hRel at CertData level (D66), manifest 2 (D67)

**D66 (checker, hRel).** Worker commits 37b76b85c..82314d764 are
cherry-picked. The lead verified attempts 4513, 4601, 4602, 4607, 4609,
4610, 4613, 4614 and 4617: SHAs match, exit 0, standard axioms, no
overrides.
- `fill_rel` (WideExact ops, batched weights, both dual folds, line folds,
  relation coefficients) has an extracted copy; its differential test equals
  z9c's relation matrix exactly on all five configurations (499,328 and
  232,320 entries).
- The WideExact model (`CertRelW`): under `Tower B` and the new premise
  w·w = B.u, the extracted `wmul` is the product in K.
- `coefM_eq`, the weight/fold identities with weightsR1, w1, w2,
  lineFoldValue and naturalLineValue, and `rel_data`.
- `p_r1_of_data_rel`: `p_r1_of_data` with hRel discharged, at the CertData
  level (6.81 GB).

Not accepted: the pb/ct-level `check_sound⁗` wrapper. Two attempts (4615,
4616) hit -M7000 while loading imports, because any importer of Sound4
starts at about 7.18 GB. A larger-cap run is declined. The wrapper waits for
an import refactor of Sound2–4, with replays. New named premises: w·w = B.u
and the limb basis; the inverse transport ti = π⁻¹; the opening limbs; the
folded-position map fp (injective); query bounds; li = lineInverse and
x16 = storedLine16X on the line relations; size equalities.

**D67 (integration, manifest 2).** Worker head 167a70d73 is merged. The
lead verified attempts 5517 and 5520.
- `AspisR1Qm31ArithmeticProbe.{Funs,Types}` were promoted bytes-unchanged
  (Funs `114552b8…`, Types `c5a08408…`, matching the host extraction source
  and the accepted sampler journal). Their generated `maxHeartbeats`/
  `maxRecDepth` options are kept as generated.
- `privacy_R1_games_spendSampler` (5517, 4.12 GB): the QM31SamplerLaw
  premise is discharged from the extracted sampler, in one closure.
- T1 `toModel_toRust`, T2 `witnessOk_toRust`, T3 `pubCorr_toRustPub` (5520).
  T4 waits for the X/R1X decision.
- To fit under the cap, `R0Z.GoodDensity` and `R0Z.StatisticalDistance`
  were narrowed from `import Mathlib` to bounded sets (imports only). The
  dependents were rebuilt. `R1Z.EventsR1P2` then failed at `card_NZ` with
  kernel memory exhaustion: the narrower imports change the `Fintype`
  instance found for Fin 32 → UInt8. An import-only probe did not help.
  The unified build is stopped there: 425 of 455 modules current, with
  `privacy_R1_games′` and `check_sound″` not current on that base.
  Their standard-axiom status from manifest 1 (D65) stands for the
  whole-Mathlib base.

Deferred decisions, recorded as open:
1. EventsR1P2: a proof-level fix of `card_NZ` (count through `card_ans`),
   or revert the narrowing and size the composition another way.
2. The module of record for `AspisR1PublicPreparation.{Funs,Types}`, which
   has 3 and 5 repo copies; `SemRowsSpend` (`decSpend`, `semRows01_spend`,
   premise `RSqueezeAnswer`) is written and waits on it.

All agents are paused. No host job is running.

### User decisions (2026-10-19 evening); D68

1. **G_R1.1:** the ≤1.3M-per-transaction target stands and is to be met by
   arithmetic savings (~120k CU on the worst case), not by rebalancing.
   Recorded in `docs/research/100bit-spend-path-20261013/design/LEAD-DECISION-G-R1-1-20261019.md`.
2. **D54.3 resolved:** the production prover's writers (value, occupancy,
   path aux, bank merge, block, node, sponge, Poseidon) are to be replaced by
   the extracted copies in `refine/`, so `builder_witness_merged` is about the
   shipped prover. Prover-side only; no on-chain change. The migration goes
   through the standing gates (codec 1,233 outputs byte-identical, the
   ordered trace, checkpoint23, the saved fixtures, the 512-witness glue
   differential) and re-pins the extracted declarations.
3. **Lead rulings on the unified build (D67 deferred items):**
   - `EventsR1P2`: proof-level fix of `card_NZ`, counting through the
     existing `card_ans` equivalence; the import narrowing stays.
   - `AspisR1PublicPreparation.{Funs,Types}`: the module of record is the
     c16 copy the accepted proofs were compiled against (Funs `e98bb123…`),
     promoted bytes-unchanged like the Qm31 probe modules.

All work lands on `research`.

### Lead acceptance of the checker wrapper (2026-10-19); D69: `check_sound''''` compiles in env J

Worker commit 12d1588e2 (branch codex/r1p-checker-wrapper-20261019) is
cherry-picked as 8944115e4. The lead verified attempts 5649 and 5700 on the
host: source SHA matches the repo (`R1Z/CertCheckSound5.lean` dacff139…),
exit 0, standard axioms only, 0 swaps; peak RSS 4,128,696 KiB and
3,607,944 KiB.

**D69.1 Why workspace A cannot hold the wrapper.** It is measured, not
assumed (`c3/wrapper-refactor/NOTE.md`). Every module stating both `P_R1`
and the extracted `check`/`fill_*` imports all of Mathlib through base
`import Mathlib` files (first AspisFormal.CircleGroupOrder). The floor is
2.498 GB of olean, about 7.1 GB RSS, against the -M7000 limit; the
CertCheckSound2–4 chain adds 0.039 GB. No R1Z split helps. Env J's narrowed
base brings the Sound3 closure to 1.45 GB. The planned Sound2–4 refactor is
withdrawn; the chain is compiled in J unchanged.

**D69.2 J rebuilds.** 5600–5621 rebuilt the 22 manifest-3 modules made stale
by the D67 narrowing (sources unchanged). J's `R1Z.CertBuildExtracted` was
the pre-D62 extraction (27f2dc76…, no `fill_own`); with lead approval it was
replaced by the repo/D62 copy (d7e06b9f…, additions only), old source and
objects snapshotted on the host, and dependents rebuilt (5623–5646). The
wrapper needed two proof-only fixes (5647, 5648 failed; 5649 green): no-op
`dsimp only [coefK]` removed, `subst hnfU` added. The theorem's statement is
the D64 wrapper's.

**D69.3 Follow-ups.** manifest-3 still records the old CertBuildExtracted SHA
and must be updated to d7e06b9f…, or joint-drive.py will try to rebuild
CertBuildIdent2/CertLiftIdent. Attempt range: the wrapper worker used J
5600–5649 and 5700 (5650–5699 belong to the round-identity worker).

**D69.4 Status.** The P_R1 checker's soundness now composes to the pb/ct
level in one build. Its premises are named, not proved: hRound/hGRound/hGBat
(in progress), the decoder facts (hup, hnq, hz, hrw) and the builder input
identifications (chain, BCondG, lift, own, relation) listed in the theorem.

### Lead acceptance of the writer migration (2026-10-19); D70: the shipped prover's writers are the extracted copies

Worker commits b321d7a60 and 3c4282257 (branch
codex/r1p-writer-migration-20261019) are cherry-picked as 97e16309c and
36ddca98e. This carries out D68.2.

**D70.1 What changed.** The trace is built by
`compile_pool_v1_pair_forest_{private_transfer,withdrawal}_merged_c1_v1`
(aspis-statement `pool_v1/pair_forest_trace.rs`), which the prover, the
wallet adapter and the pool gate all call; `prover.rs` is untouched. Every
cell of both banks and the merged C1 is now written by the three copy crates
(`refine/{writers,blockwriters,poseidon}`), and the bank merge uses the
extracted `merge_check`/`merge_copy`. The glue (`pair_forest_copy_builder.rs`)
is the harness glue verbatim, enforced by `refine/migration/check-glue-text.py.txt`
(copy SHAs plus verbatim text; two deliberate edits made it fail). The copies
are host-only dependencies (`cfg(not(target_os = "solana"))`); no program or
verifier source changed. The pre-migration compiler is kept as
`pair_forest_trace::reference` behind the audit-only feature
`pool-v1-pair-forest-writer-reference`.

**D70.2 Gates** (`refine/evidence/writer-migration-20261019.json`, host,
`--release -j 4`, MemoryMax 8G, no swap): codec 1,233 stdout byte-identical
(3ef16b12…); ordered trace 583 calls identical; checkpoint23 23 passed,
stdout byte-identical; saved fixtures pass (glue, 6 forest tests, four
deterministic masked proofs byte-identical between f458169f7 and b321d7a60);
512-witness glue differential passes with D61's mutation counts. Because the
glue harness now partly compares the copies with themselves, the worker added
`tests/pair_forest_writer_migration.rs`: new compiler vs retained reference on
both fixtures, 512 random witnesses and 2,046 mutations (31 kinds, 18
outcomes), passed.

**D70.3 Pins.** The copy source files are unchanged (writers 20b9aed5…,
blockwriters f5ca7ae8…, poseidon 2591c007…), so no extracted declaration needs
re-pinning; `builder_witness_merged` is now about the shipped prover's
writers. Only the copies' Cargo.toml lost `[workspace]` (they are root
members now); the extraction scripts restore it in their scratch copy.

**D70.4 Open.** The Rust glue still matches Lean `copyCellMerged` by
generated table, verbatim text and differential test (D61 standing). T4
(Wspend⁺ → RustWitness map) is untouched. Root and five tool lockfiles
gained three path packages; no SBF source changed, but an SBF
reproducible-build check is due before the next artifact pin.

### Lead acceptance of the build fix (2026-10-19); D71: manifest 2 complete on the narrowed base

Worker commits 30cd8256e, 28343384b, 21fa85681 (branch
codex/r1p-build-fix-20261019) are cherry-picked. The lead verified attempts
5532 (`card_NZ`, EventsR1P2 5746651a…, 3.62 GB), 5544 (`semRows01_spend`,
4.13 GB) and 5547 (`privacy_R1_games′`, 3.61 GB): source SHA matches the
repo, exit 0, 0 swaps, standard axioms.

**D71.1 card_NZ (D68.3 carried out).** `card_NZ_of (i : Fintype NZ)` counts
through `Equiv.optionSubtypeNe 0 : Option NZ ≃ OracleAnswer`,
`Fintype.card_option` and `card_ans`; the foreign instance enters only through
`Subsingleton (Fintype _)`, so the kernel never compares instances by
reduction. `card_NZ`'s statement is unchanged; the import narrowing stays.

**D71.2 PublicPreparation and SemRowsSpend.** The promoted c16 copy
(`extracted-public-preparation-c16-20261019`, Funs e98bb123…) is the one
used; manifest-4 overrides the generator's alphabetical pick (the
bridge-prepared-3335 copy) and lists the override. SemRowsSpend needed
`open AspisR1PublicPreparation`; `semRows01_spend`, `row_refines`,
`begin_refines_decSpend` and `begin_agrees_dec` check, with `RSqueezeAnswer`
a named premise.

**D71.3 State.** All 462 modules (manifest 2's 455 plus the SemRowsSpend
closure) are current on the narrowed base (manifest-4, CertBuildExtracted at
d7e06b9f as D69.3 asked). Seven Cert modules are current by dependency
fingerprint (their inputs are byte-identical after D69), not by a fresh
compile. PrivacyR1P now peaks at 3.6 GB (6.79 GB in manifest 1). The roots
`privacy_R1_games′` (5547) and `check_sound″` (5616) check with standard
axioms. The worker's driver is range-confined (`joint-drive-range.py.txt`);
two refused records (exit 67) sit in the shared attempts.jsonl.

**D71.4 Axiom finding.** The 462-module audit (3,150 reports) finds one
non-standard axiom, `core.fmt.Formatter` (an Aeneas opaque type), in
`AspisV8R19.SamplerWordRead.{unwrap_success, read_success}` (5414). It
predates this job and no root theorem depends on it. Ruling: those two
lemmas are not release-root material; any future root that imports them
fails the axiom audit until the Formatter use is removed from the extraction.

### Lead acceptance of the round and G-batch identities (2026-10-19); D72: `check_sound_gbat`

Worker commits 3e68b5215, 2c86d92c9, c4d68034a, e4b80904f (branch
codex/r1p-checker-rounds-20261019) are cherry-picked. The lead verified
attempts 5655 (`check_sound_round`, da6644a2…) and 5661 (`check_sound_gbat`,
89b82ff9…) on the host: SHAs match the repo, exit 0, 0 swaps, about 4.12 GB,
standard axioms. c4d68034a was committed before compiling (host unreachable)
and says so; e4b80904f records its compile.

**D72.1 Result.** `R1Z.CertCheckSound.check_sound_gbat` is `check_sound''''`
(D69) with hRound, hGRound, hGBat and hz discharged.
- `CertRoundK`/`CertRoundIdent`: a Mathlib-only model of the Rust
  `round_row`/`tail_row` loops (`srcRoundR`) and the symbolic identity
  `z4c_srcTape` for every lane, row r ≠ 0 and limb, from the R0Z.PureRounds
  closed forms.
- `CertGBatK`/`CertGBatIdent`: `gbatP` models z9.rs `unit_functionals` for
  the G lane; `gbat_cell` identifies every support cell of the batched image,
  with weights tied to `weightsR1`/`w1` through `wtP_ident`/`w1P_ident`.
- hz holds with no new premise: the OOD points are `Alimb zz` values, hence
  in K₄.

**D72.2 New named premises (replacing the identities).** `hRent`, `hGent`:
each column entry of `pb.round`/`pb.ground` packs to the `srcRoundR` value.
`hGBent`: each `pb.gbat` cell's eight limbs combine in `wb` to `gbatP`.
`X18`/`hX18`: the stored first-line points at the opened folded positions (an
input table, D59.2 ruling). `hfo`: every listed folded position is opened.
These are statements about what the prover wrote, of the same kind as hRel
before D66; they are discharged by extracted copies of the round and gbat
column writers with Aeneas entry lemmas (the `fill_rel` pattern). That job is
next on the checker track.

**D72.3 Still open on the checker.** Decoder facts `hup` (sampler/transcript),
`hnq`, `hrw` (pb construction); the builder-input premises inherited from
`check_sound''''`. The six new modules need manifest entries before the
final replay.

### Lead acceptance of R-retry and G-sim (2026-10-19); D73: the retrying prover and the explicit simulator exist in Rust

Worker commits a4aca2a1e..bcba80117 (branch codex/r1p-retry-sim-20261019, six
commits) are cherry-picked as ad57ac42f..eae26c314. Rust only; no Lean
compiled. Host runs at d951c0681, after rebasing onto the optimised verifier
(CU savings, 7133365cc); evidence `r1p-retry/evidence.json`,
`gate2-d951c0681.json`, `simgate1-d951c0681.json`.

**D73.1 R-retry (D38.3).** The P_R1 check runs in `prove_from_semantics`
after the queries and ρ are drawn, before any output buffer exists; the
verdict is emit-success plus the D57 extracted checker on the extracted
builders' columns (`fill_tq`, `fill_lo`, `fill_own`, `fill_rel`).
`prove_masked_retrying` caps at N = 8, fresh OS secrets per attempt, nonce
burned durably first, `AttemptsExhausted` publishes nothing; `r1p-check`
implies `private-leaf-salts` (compile_error guard); only a verdict bit and
durations leave the check, and panic messages inside it are suppressed.
Tests: forced 7 rejections then accept (8 distinct nonces, G-mask, salt and
C1 roots; proof verifies), exhaustion, real-check path. Measured: 32/32 OS
attempts accepted and verified; 41.2 s per attempt (proving 5.5 s, check
35.8 s: emit 14.5, builders 9.95, checker 11.1 with overflow checks on).

**D73.2 G-sim (D44.3).** `sim::sim_e` takes the public statement and a seed
only, runs the ideal game's P-only loop (cap 8), and programs the oracle at
the transcript reads, opened leaves and path nodes. The simulated proof
passes strict tx1+tx2 and dense under the programmed oracle and is rejected
under the real hash; dropping S₀ or the round-9 shift is rejected. 4 seeds:
33.6–35.5 s (P_R1 32–34 s; ≈1.5 s without the check), 442–450 addresses
programmed, all read. The verifier is generic over the hash; no verifier
injection was added. `CORRESPONDENCE-G-SIM.txt` maps each step to GamesR1,
RefPayload, Shift, PayloadSplit, Partition, JointTrace: a reading, not a
proof. G-sim is closed as specified in D44.3.

**D73.3 Edits outside the stated scope (reviewed, accepted).** `verifier::Error`
gains `Rejected`, `AttemptsExhausted`, `Entropy` under `cfg(feature="prover")`
only, so the SBF build's enum is unchanged. Root `exclude = ["docs"]`: checked
with `cargo metadata` that the three D70 copy crates remain members (explicit
members win). Release overflow checks for the extracted checker/builder
crates (host only). z4 probe files changed by visibility only, so their
SHA-256 no longer match the D57 differential receipts; the D57 receipts
stand for the earlier bytes.

**D73.4 Mismatches with the Lean games (lead rulings).**
1. ActivePole: Rust surfaces it as `Error::Semantic` and aborts; Lean
   `realGame` charges it (D40.3) and continues to the next attempt. Ruling:
   the Rust loop must treat a pole as a rejected attempt (consume one of the
   N = 8, publish nothing). The fix touches the aspis-statement copy-helper
   builder; it is a follow-up job.
2. Exhaustion: the worker reports the same shape; the follow-up must state
   Lean's exhaustion behaviour from the source and make Rust match it.
3. P_chk ⇒ P_R1 still rests on the open premises of the checker (D72.3);
   z9e's public-data builders are ports from cost-probe 1822c2ced and must be
   re-checked against the current prover.
4. Tape law (the simulator uses the prover's expander; Lean assumes a uniform
   tape) and formula equality for inactive-sum and batched cells remain
   R-commit and G-ref.

**D73.5 Cost note.** The honest prover now takes about 41 s per attempt,
almost all in the P_R1 check (D38 measured 22.6 s for an earlier, unchecked
port). A prover-speed job (overflow-check cost, builder conversion) is
optional and does not affect soundness or privacy.

### Lead acceptance of the pole/exhaustion fix (2026-10-19); D74: the Rust retry loop rejects exactly Lean's failed attempts

Worker commit 6bd605419 (branch codex/r1p-pole-retry-20261019) is
cherry-picked. Rust only, prover side; evidence `r1p-retry/evidence-pole.json`,
`POLE-EXHAUSTION.md`; host lib tests 27/27 (3:58, 506 MB, 0 swaps).

**D74.1 Lean behaviour (read from source, POLE-EXHAUSTION.md §1).**
`realGameP` publishes the first attempt with `P ∧ VR1 ∧ exh = false`
(GamesR1P.lean:184). A pole (¬NoPole at λ = sem 0, χ = sem 1) and a mask-decode
exhaustion (`MaskSampleExhausted` on either 16-try stream) each skip the
attempt and consume it. After N failures the game outputs the constant
`failView` (GamesR1P.lean:185), the same constant as the ideal side. Ruling:
"publish nothing" (`AttemptsExhausted`, no bytes) is the Rust reading of that
constant; no byte encoding of `failView` is needed.

**D74.2 Rust now matches.** Pole → `r1_wire::Error::ActivePole` (no row,
side or value; exists only under `r1p-check`) and mask exhaustion both map
to the detail-free `Error::Rejected` and consume one of the 8 attempts. Other
errors still abort. Default-feature codegen objects of the cost-probe lib are
identical before and after (9/9; rlib metadata only differs), so the verifier
build is unchanged.

**D74.3 Finding: the old Rust pole check was weaker than Lean's.**
`build_copy_logup_helper` inverted only nonzero-weight slots, while Lean's
`NoPole` covers all four slots of every copy-active row including zero-weight
and empty ones; and the prover's copy rows put an endpoint in the first
zero-weight slot (on a withdrawal, row 523's PrivateTransferOnly producer is
overwritten). On the fixtures, 42 (transfer) and 50 (withdrawal) distinct
nonzero χ values, plus 0, were Lean poles the Rust loop did not reject. The
new `host_semantic::no_pole` computes Lean's static-slot `copyRowValues` and
checks every slot, so the Rust pole set is Lean's `poleSet` and D40.3's ε_pole
is unchanged. Tests: pole on attempt 1 (attempt 2 published, verifies strict
and dense), pole on attempt 8 after 7 rejections (exhausted, 8 nonces,
nothing published), forced mask exhaustion, NoPole on both fixtures, all 136
static copy links against `COPY_LINKS`.

**D74.4 Open.** The Rust `no_pole` ↔ Lean `VR1` match is a reading of the
sources (a private `tuple_value` copy tested indirectly; `copyLinks` vs
`COPY_LINKS` not re-derived; `h.build w` = compiled trace is G-ref). Other
per-attempt failures still abort with no Lean counterpart: QueryScan
(`Error::Transcript`; Lean's `kstarOf` is total) and Semantic errors in mask
application, salts or builders; these join R-wire/R-commit with a required
probability or impossibility argument. CORRESPONDENCE-G-SIM.txt §8 (a)/(b)
are closed by this entry. SBF rebuild not run (host default-feature objects
identical).

### Lead acceptance of the column writers (2026-10-19); D75: `check_sound_cols`

Worker commits ef845ca95 and d69ee5dbd (branch
codex/r1p-column-writers-20261019) are cherry-picked. The lead verified
attempts 5754 (`fill_round_entries`, 3.83 GB), 5755 (`fill_gbat_entries`,
3.80 GB) and 5756 (`check_sound_cols`, 4.06 GB): SHAs match the repo, exit 0,
0 swaps, standard axioms. 5751 and 5753 failed and were fixed by source
changes.

**D75.1 Result.** `R1Z.CertCheckSound.check_sound_cols`
(R1Z/CertCheckSoundCols.lean) is `check_sound_gbat` (D72) with `hRent`,
`hGent`, `hGBent`, `X18`, `hX18` removed and the extracted writer runs added:
`fill_round … = ok pb.round`, `fill_round … = ok pb.ground` (own-column
descriptors reused), `fill_gbat … = ok pb.gbat`, plus the input slice `x18`
with named premise `hx18` (`x18[f] = storedFirstLineX18 (fp f)`, D59.2 input
table) and `hfo`. The entry lemmas rest on the closed form `pcR_closed`
(coefficient d of (b + wX)^e) and the builder-4 specs; loops by invariants
or structural induction, no concrete-size evaluation.

**D75.2 Extraction.** Builders 5 and 6 appended to `c3/build/src/lib.rs`,
re-extracted with the pinned Charon/Aeneas under caps; `CertBuildExtracted`
(d7e06b9f…) and `CertRelExtracted` (7ce94171…) checked byte-identical
(`split-cols.py.txt`). Each `let x = if …` selection was moved into its own
function to avoid do-notation join points (behaviour unchanged; all evidence
is for the final source). `CertColExtracted.lean` 81a2334a… committed as in
D66; `build.llbc` by SHA only.

**D75.3 Rust evidence.** On the five D66 configurations the new writers equal
z9c's round, G-round and G-batch columns with 0 mismatches (up to 3.2M,
2.1M, 2.6M entries); teeth: clearing inactive flags changes ≈1.0–1.15M round
entries, moving one x18 point changes 13–16k gbat entries. Wired into the
prover's P_R1 check (z9e); a test records a real attempt's challenges and
finds 0 column mismatches; 22/22 lib tests; gate 8/8 accepted and verified
(37.8 s per attempt, check 33.5 s).

**D75.4 Remaining on the checker.** Decoder facts `hup`, `hnq`, `hrw`; the
named input premises (π/`ti`, OOD and stored points, `inact`, `x18`, `x16`,
`li`, `hW`/`hwb`, `Tower`); the builder-input premises inherited from
`check_sound''''`; manifest entries for CertColExtracted, CertRoundFill,
CertGBatFill, CertCheckSoundCols (and D72's six) before the final replay.

### Lead acceptance of the binary-format read budget (2026-10-19); D76

Worker commit 6decf88a8 (branch codex/r1p-readbudget-20261019) is
cherry-picked. The lead verified attempts 5757 (`CommitReadsR1`, 2252d377…,
2.48 GB), 5759 (`ReadBudgetR1`, 9f1304bc…, 2.46 GB) and 5760 (`FinalR1P`,
olean byte-identical to before, so PrivacyR1P was refused as an unchanged
rerun and its 5547 build stands): SHAs match, exit 0, 0 swaps, standard
axioms. Shared source `CommitReadsR1.lean` replaced in J (old source and
objects snapshotted on the host).

**D76.1 Count.** Per attempt the binary commitment phase reads 3·2^18 salts,
3·2^18 leaves, 3·(2^18−1) = 786,429 parents and 3 seeds plus the expander
blocks: Mc = 2,359,296 + E₁ + E₂ (eight-way: 1,685,214 + E₁ + E₂). An
instrumented prover run (`readbudget_count`, one fixture) matches the source
count exactly in both formats. Multiproof assembly hashes nothing.

**D76.2 Bound.** `mc_le : 115 + Mc ≤ 2^22` (the old 2^21 is shown false at
worst-case counts, `mc_gt_2_21`). No theorem statement changed: the privacy
roots take the read count as a parameter. `ReadBudgetR1.r1_games_error_le`
proves the `privacy_R1_games_spendSampler` error ≤ 2^-109 + 2^-137 at the
binary count; the D41 three-term form is ≤ 2^-165 (was 2^-166). Total
privacy error unchanged at ≈ 2^-109 (pole term dominates). The old D41
numerals in `R0Z/FsAbortR1` (`r1_error_N8` at 8·2^21) are unused and kept;
`r1_error_N8_bin` is the binary version. Ruling: retire the old numerals at
the next FsAbortR1 touch, not now (every privacy root imports it).

**D76.3 Remaining for the format change on the privacy side** (PROOF-SIZE-
OBLIGATIONS items 5–6, now scoped): `GamesR1P:45–53` (`NodeIdx` over
`Fin 8`), `LayoutR1P{,2,3}` (`childQ`, `rootChild`, `nodeBytes` with tag
`0x18` and eight children, `openedQ` with `u / 8^(level+1)`), `EventsR1P`
(`ROpen`, `RComLog`); the `0x12` binary node-tag disjointness; the
retrying prover `prove_masked_retrying_with` still calls the eight-way
prover (the adoption job covers this). After the layout rewrite, worst-case
n1 = 2,457,717 ≤ 2^22 and `r1_games_error_le` applies directly.

### Lead acceptance of the binary privacy layout (2026-10-20); D77

Worker commits bba92e316, 5a3eb2d90 (branch codex/r1-privacy-layout-20261019,
Codex, after the stopped Claude agent's WIP 2d7d47218) are cherry-picked.
Attempts 6000–6027 in env J, 20 green (10 failed sources fixed by source
changes, none rerun unchanged); the lead checked the last (6027,
`PrivacyBoundR1PBin.privacy_R1_games_binary_bound`, 4.15 GB, 0 swaps) and the
JSONL: every green module has standard axioms.

**D77.1** The concrete layout chain is duplicated in `Bin` modules
(`LayoutR1PBin`, `LayoutTagR1PBin`, `EventsR1P*Bin`, `FinalR1PBin`,
`PrivacyR1PBin`, `PrivacySamplerSpendBin`, `PrivacyBoundR1PBin`, …), the
eight-way API untouched and still compiling. Proved: `n1_worst_case`
(n1 = 2,457,717 including both binding reads), `batchReadSet`/
`batch_toFinset`/`batch_length` (exact per-batch read sets with the
deduplication `ROpen` requires), and the binary privacy error ≤ 2^-109 +
2^-137 (N = 8, q ≤ 2^64) from the unchanged `ReadBudgetR1` bound (D76).

**D77.2 Obstruction, accepted as conditional.** Unconditional disjointness of
binary node records from arbitrary abstract transcript records is false
(`LayoutObstructionR1PBin.binary_duplex_overlap`, kernel-checked: an
`addrWith (.absS 0)` record with a 31-byte framed message equals a 65-byte
node record). Separation holds for every commitment record class and
eight-way nodes unconditionally, and against transcript records under the
named premise `TranscriptNodeLengths` (`LayoutR1PBin.nodeBytes_ne_transcript`).
Discharging that premise from the actual wire encodings (framed length ≠ 31,
payload/final lengths) is an R-wire item; the soundness-side commitment
model reports the same shape of obstruction at `verifier.rs:382` (public
bytes hashed verbatim) and will carry the same premise until the wire
lengths are proved.

**D77.3 Remaining for the format on the privacy side:** the simulator layout
(Lean `simE`/ZF2 and Rust `sim.rs`, now ignored in the adopted build) and the
`TranscriptNodeLengths` discharge.

### Lead acceptance of the binary simulator (2026-10-20); D78

Codex job cx-sim-bin (d2bda2ae1) is cherry-picked. Lean: a binary read-set
bridge and `privacy_R1_eff_binary` compile in env J (attempts 6100, 6105,
6106 verified: exit 0, standard axioms, 0 swaps), bound 2^-109 + 2^-137 on
the D76 budget; the explicit simulator now programs the oracle at the binary
multiproof read set (D77 `batchReadSet`). Rust: `sim.rs` ported to the
compact binary format, its four tests un-ignored and passing; four timed
simulated proofs pass strict tx1+tx2 and dense under the programmed oracle,
fail under the real hash, 36.4–38.4 s each, every programmed address read.
`CORRESPONDENCE-G-SIM.txt` updated. PROOF-SIZE-OBLIGATIONS item 5 is closed.
Remaining on the privacy side for the format: `TranscriptNodeLengths`
(D77.2; job cx-wire-len) and the inherited source-refinement premises.

### Lead acceptance of the wire-length separation (2026-10-20); D79

Codex job cx-wire-len (d0920f9a5) is cherry-picked. The D77.2 premise
`TranscriptNodeLengths` is discharged for the concrete R1 wire: the privacy
module (env J attempt 6251, standard axioms) proves binary node preimages
separate from the typed transcript records, the extracted semantic public
bytes, the ASF8 request and the concrete privacy carrier. Lengths
(`design/WIRE-LENGTHS-20261020.md`): semantic public bytes 1,455 (transfer)
/ 1,427 (withdrawal), ASF8 1,880, ASQ8 320; none is 31 or 65. The same
facts, in four soundness modules compiled locally (19 audits, standard
axioms), discharge the Bin commitment model's public-byte length premise.
What the separation does NOT cover: the unrestricted abstract literal
message carrier still admits arbitrary lengths; the result applies through
the typed records and the extracted parsers, so the R-wire execution
correspondence (that the deployed transcript only ever hashes those
records) remains the carrying obligation, with the ASQ8 decoder extraction.

### D79 addendum (2026-10-20): three more hashed record classes

Codex job cx-record-classes (4dd8a0a64): the 57,607-byte compact proof, the
1,880-byte ASF8 account and the 1,758-byte checkpoint checksum input are
proved to have those fixed lengths and to separate from 65-byte binary nodes
and 31-byte frames, on both trees (15 local audits; env J 6302–6303, 14
audits; standard axioms; privacy roots unchanged). With these, the extended
class inventory covers all 31 tx1 digest sites of WIRE-TX1. The carrying
obligation is unchanged: that deployed execution hashes only members of the
inventory (R-wire whole-tx1 refinement, then tx2).

### Lead acceptance of the premise reduction (2026-10-20); D80

Codex job cx-priv-premises (265ab669b) is cherry-picked. Ten theorems
(env J 6322, 6325, 6326 verified: standard axioms, 0 swaps, ≤ 3.8 GiB)
reduce the binary-format refinement premises — the commitment grammars
(RCommitBytes), the opening batches (ROpen), the ordered logs (RComLog) and
the root causality (RCausal) — to explicit remaining source facts, tabled in
`r1p-premises/PREMISES-20261020.md`. One counterexample is recorded: raw
leaf-read calls cannot be identified with ROpen's duplicate-free batches
when a folded leaf index repeats, so the identification goes through the
deduplicated batch (D77's batchReadSet), not the raw call list. Remaining,
per premise: the soundness-tree imports (the Bin grammar lives on the other
tree; a shared module is the next hygiene step), carrier transport,
source-loop simulation, normalisation and the execution-log correspondence
— the same items R-wire/R13 carry on the soundness side. No premise is
fully discharged yet; each now names its exact remaining fact.

### Lead acceptance of the shared binary record grammar (2026-10-20); D81

Codex job cx-shared-grammar (1f557c18f) is cherry-picked. One module of
record, `docs/research/100bit-spend-path-20261013/lean/SharedBinaryRecordGrammar.lean`
(node 0x12 ‖ two children, leaf tag/salt layout, the D79 record classes and
lengths), enters the unified manifest; two bridging modules prove the
privacy `LayoutR1PBin.nodeBytes`/leaf layout/wire tables and the soundness
`BinMerkle32Path.nodeInput`/leaf grammar equal to it (with the explicit
Fin 256 → UInt8 transport). All three compile in env J (and the soundness
bridge locally); 21 audits, standard axioms, 0 swaps. The dependent privacy
roots were fingerprint-refused (unchanged inputs), so their builds stand.
Existing separation proofs carry over by rewriting; no statement changed.
The two trees now share one grammar; the remaining cross-tree item is the
R-wire execution correspondence.

### Lead acceptance of the final R1 privacy composition (2026-10-20); D82

Codex job cx-priv-final (678846822) is cherry-picked. `R1Z/PrivacyR1Final.lean`
(env J 8000, 8004, 8008 verified: exit 0, standard axioms, 0 swaps) composes
privacy_R1 / games′ / the binary simulator with D76–D81 and the query-scan
abort into one theorem for the adopted binary format. Error at the deployed
parameters (N = 8, q ≤ 2^64, worst-case counts): ε ≤ 2^-109 + 2^-137 +
2^-454 — the LogUp pole ≈ 2^-109 dominates; adversary hit 2^-166.8, prover
collision 2^-206.5, mask-word exhaustion ≈ 2^-473.4, frozen/public-digest
hit 2^-230.8, ideal programming 0, query scan 16·2^-486 = 2^-482 (eight real
and eight simulator attempts; the sharpened per-scan bound is 2^-486).

**The privacy definition of done** is the premise checklist in
`r1p-final/PRIVACY-FINAL-20261020.md` ("Open obligations: exact top-level
source interfaces"): builder refinement (D46/D51), Sem1Uniform's wire form,
the classical-ROM address domain and observer map, R-causal in D80 form,
R-commit for roots/nodes, leaves, bindings, seeds, salts, expanders, equal
fibres and exhaustion counters, R-wire coin carrier, batches, ordered log
and typed-record membership, the builder/checker/retry coupling (D75), the
simulator coupling (G-sim R-wire), and the query-word history/agreement off
the scan events. Every one is a source-to-model refinement fact; none is a
probability or rank fact. This list replaces D42.5 as the tracking list.

### Lead acceptance of the builder refinement (2026-10-21); D83

Codex job cx-builder-ref (ed85b028b..5b1a6582b) is cherry-picked. 39
theorems in five R1Z modules (env J 8400–8446, standard axioms, 0 swaps):
Rspend⁺ → ModelRel with the sentinel, digest, append-carry and PairRight
obligations derived; canonical witness/public maps and base typing; all four
`BuilderSoundOn` fields (baseTyped, lanes, helperSum, helperInactive) for the
extracted merged builder; the fixed D18 transport; a conditional source
identification handoff (`r1p-final/BUILDER-REFINEMENT-20261021.md`). The
first row of the D82 checklist is reduced to the shipped-prover
identification: Charon extracts both compile entry points; pinned Aeneas
rejects `validate_forest_poseidon_rows` (labelled break to an outer loop,
lines 158–197). Ruling: the prover is not frozen, so the break is
restructured (early-return helper) under the byte-identical fixed-seed gate
(job cx-builder-ref2), then the shipped records/public mapping, the Rust
glue equality and the S2 transport complete SourceIdentification.

### Lead acceptance of the ROM rows (2026-10-21); D84

Codex job cx-priv-rom (ee6ad61d3, 6323a578a, 59f374e0d) is cherry-picked
(env J 8604, 8605, 8607 verified: standard axioms, 0 swaps; 8606 failed and
was fixed by a source change). New modules `RomFiniteBin`, `RomGrammarBin`,
`RomObserverBin` construct the finite classical ROM tables, prove
address-domain membership from typed read coverage over the binary grammar,
fix qmax = 2^64 and prove the source observer's decision function is
preserved. The endpoint `PrivacyR1Final` is edited (the one exception to
"no edits to existing modules", accepted because the statement strictly
narrows and nothing imports it): the premises `R_rom_classical`,
`R_rom_address_domain` and `R_rom_adversary_budget` are removed and replaced
by one source premise, `R_wire_read_coverage` (universal typed read
coverage). Three D82 checklist rows are discharged; the ROM side of the
privacy proof is now closed except that coverage fact, which belongs with
the other R-wire source items (`r1p-final/ROM-ROWS-20261021.md`).

## D85 — causal row: generic wire interface is too permissive (2026-10-20, lead)

Reviewed `codex/cx-priv-causal-20261021` (landed as c94f789bf..ae629bd5d).
`R_causal_D80` stays open, and for a reason that changes the plan: the generic
`R1Wire`/`R1ProverP` interfaces carry none of the D48.3 phase restrictions, so
`prematureC2_not_causal` exhibits an admissible wire whose row-zero absorb
reads C2's root. No execution-order argument can discharge causality over all
admissible wires. The fix is a model refinement, not a proof: construct the
concrete protocol wire/prover (phase-restricted frame, payload, decode and leaf
values) and prove `RCausal` for that instance, with the final theorem stated
over it. Symbolic binary-tree layer facts (`CausalTreeOrderBin.lean`) landed
as independent progress. `PrivacyR1Final.lean` unchanged. Forbidden-construct
scan clean; host attempts 8802/8804 standard axioms, zero swap, RSS < 3.6 GB.

## D86 — builder refinement: S2 transport certified; restructure held for ELF gate (2026-10-20, lead)

Landed from `codex/cx-builder-ref2-20261021`: the shipped S2 row transport is
proved equal to the D18 arithmetic reference by Kani and refined in Lean via
an extracted reference (`R1Z/BuilderTransport*.lean`, env J 8450/8452,
standard axioms). Held back pending a gate: the restructure of
`validate_forest_poseidon_rows` in `aspis-statement/src/pool_v1/pair_forest_trace.rs`
passes the D83 prover gates (fixed-seed bytes, codec, ordered trace, both
differentials, P_R1 8/8), but its frozen-source check omitted
`aspis-statement`, which the verifier and Pool link. The continuation must
show the default, devnet and Pool ELFs byte-identical to the frozen pins
before it merges. `builder_refinement_D46_D51` stays open: Aeneas hits borrow
blockers in `records` and the Poseidon lazy external layer; the continuation
moves those to per-function Kani harnesses with contracts and stubs.

## D87 — causality proved over the phase-restricted interface (2026-10-20, lead)

Landed from `codex/cx-priv-phase-20261021` (note `r1p-final/PHASE-CAUSAL-20261021.md`).
`PhaseCausalityBin.R_causal_D80` proves the endpoint's causal premise, in its
exact position-indexed form, for every `R1PhaseWire`/`R1PhaseProver` at all
answer vectors, from a symbolic stage schedule (no position enumeration) and
the binary-tree order facts. Leaf dependencies are proved on the actual
`HonestView.prepare`, `MaskLayout` and `Batched.q1` maps (C1's 27 columns
challenge-independent; C2 after rows 0–1; folded fixed after row 29), and a
prefix-dependent QueryScan and block-local decoder are constructed.
`prematureC2_excluded` confirms the D85 wire cannot inhabit the interface.
The premise in `PrivacyR1Final` is therefore reduced to one modelling join:
show the shipped encoding inhabits the phase interface — (1) message encoding
from `JointView.view` with its dependency proofs, (2) sampler/parser identity,
(3) leaf encoder identity with the shipped C1/C2/folded leaves, (4) execution
refinement of the hash-call order. `PrivacyR1Final.lean` unchanged. Eight
modules, 31 theorems, standard axioms, all attempts zero swap, RSS < 3.6 GB.

## D88 — concrete phase model built; final theorem to be stated over it (2026-10-20, lead)

Landed from `codex/cx-priv-phase2-20261021` (`r1p-final/PHASE2-JOINS-20261021.md`).
A concrete Lean phase instance now exists: logical transcript encoding with
frame/payload/final locality, symbolic semantic and batched message prefix
lemmas, block samplers, first-22-distinct parsing, S2 leaf encoders and
padding (`PhaseProtocolInstanceBin`). Its `causal_premise` proves D80
causality at all answer vectors, and `endpoint_wire` shows its wire is
definitionally `RomFiniteBin.wire (baseWire base) …` for the selected base.
`PrivacyR1Final` is unchanged: its `base`/`Pr` are arbitrary, and the D85
witness survives the ROM wrapper, so no execution-only premise can replace
`R_causal_D80` at that generality.

Lead ruling (consistent with "the proved Lean protocol is the spec"): the
release privacy theorem is stated over the constructed protocol model.
A new endpoint module specialises `PrivacyR1Final` to the constructed
base/Pr and discharges `R_causal_D80` by `causal_premise`. The Rust-to-model
correspondence (sampler, field-guard and rejection behaviour, FFT,
serialisation, reached-query history, execution order) belongs with
`SourceIdentification`/builder refinement as source joins, not with
causality. Seven modules, 57 standard-axiom audits, zero swap.

## D89 — release privacy theorem over the protocol model (2026-10-20, lead)

Landed from `codex/cx-priv-endpoint-20261021`
(`r1p-final/PRIVACY-PROTOCOL-ENDPOINT-20261021.md`, verbatim statement there).
`PrivacyR1FinalProtocol.privacy_R1_protocol` specialises `PrivacyR1Final` to
the constructed phase protocol and proves
`ZK_FSS … (modelError … + 16/2^486)` with
`modelError … + 16/2^486 ≤ 2^-109 + 2^-137 + 2^-454`.
Removed at the instance: `R_causal_D80`, all eight `R_commit_D80` families,
`D/ι/hι/R_wire_Sem1Uniform`, `R_wire_read_coverage`, and the public-width
assumption (exact ROM width chosen). Lengths, typed coverage and joint
satisfiability of the construction-owned checks are proved with an explicit
structural instance and a real statement witness, so the theorem is not
vacuous on that part. Remaining premises are all source and execution joins:
packing/public domain and builder soundness; tape fibres, exhaustion,
counters and budgets; coin carrier, normalised batches and ordered log;
source experiments, randomness and observer; real builder/checker/retry
coupling; ideal simulator coupling and reached-query history. Owners in the
report's table. 21 standard-axiom audits, zero swap.

## D90 — builder refinement part 3: ELF gate passed, components proved (2026-10-20, lead)

Landed from `codex/cx-builder-ref2-20261021` (the D86 hold is released).
Rebuilt from the final source, all three programs are byte-identical to the
frozen pins (default `dfc2a91a…`, devnet `fb2fc048…`, Pool `121f3e29…`),
covering the `pair_forest_trace.rs` restructure and the cfg(kani) references
added to `pair_forest_copy_builder.rs` and `poseidon2.rs`. Six Kani
projections cover all 20 `records` fields; the raw-word leaf and the
decomposed Poseidon external layer (four-lane mat4 proved for all inputs,
then used as a verified stub) are proved equal to owned references, which
translate and compile in env J (9200, 9202, 9203). An extracted-reference
scalar projection theorem is added. `builder_refinement_D46_D51` stays open:
deployed admission/public mapping, the full canonical mapping (including
empty-root meaning), Rust glue equality and the final `SourceIdentification`
assembly remain. Note for candidate adoption: these shipped-file edits must be
carried onto the candidate freeze branch and its ELF pins rechecked.

## D91 — query-history split: ideal side proved, real side needs a collision charge (2026-10-20, lead)

Landed from `codex/cx-priv-history-20261021` (`r1p-final/PRIVACY-HISTORY-20261021.md`).
The ScanCoupling premises are split into a `ModelExecutionJoin` (execution
and agreement only, with fixed model events) and model mass laws. On the
ideal side it proves the LE low-18-bit independent-word law, the symbolic
first-stop/failure bridge and the scan bound on the constructed ideal
experiment's exact randomness, and discharges the ideal law in
`PrivacyR1FinalProtocolHistory`. Two findings: (a) deleting the probability
fields while leaving arbitrary exception events would be vacuous (constant
events join anything), so events must be fixed model events; (b) on the real
side, shared-oracle self-loop histories fail with certainty, and a
uniform-ROM scan from a fixed state has failure mass ≥ 2^-256, above the
independent-word bound. `real_model_history_law` is therefore kept.

Lead ruling: the per-history bound is false as stated, and that is not a
privacy problem. The real-side law is restated over fresh-word histories,
with the excluded repeated-read and collision events charged once as an
explicit ROM collision term (order q²/2^256) added to the privacy error. The
final error, now ≤ 2^-109 + 2^-137 + 2^-454, gains that term and stays far
below 2^-100. Six commits, seven modules, 48 standard-axiom audits, zero swap.

## D92 — prover commitment: refactors merged after ELF gate; SHA-256 callback (2026-10-20, lead)

Landed from `codex/cx-prover-commit2-20261020` (reports
`r1p-final/PROVER-COMMIT-20261020.md`, `PROVER-COMMIT3-20261020.md`). The
translating salt-loop and expander refactors (shipped `aspis-r1-cost-probe/src/prover.rs`,
`aspis-prover/src/state_only_{entropy,hiding}.rs`) are kept. Fixed-seed proof
bytes are identical, with 33/33 library/D78 tests and 8/8 P_R1, and all three
frozen ELFs were rebuilt byte-identical (`cmp`, evidence
`prover-commit3-20261020/frozen-source-check.json`). 26 subsidiary
theorems, standard axioms. Nine checklist rows stay open: the prover's
`HashFn` is SHA-256 (`HOST_HASH = host_hashv`), not Poseidon2, so D90 cannot
stub it. Lead ruling: in the model this callback is the random oracle, so
the Kani route is a symbolic memoised oracle (fresh `kani::any` per new
input, cached for repeats) shared by the shipped code and the reference. That
gives equality for every oracle function on the queried points without
postulating any property of SHA-256.

## D93 — correction to D91: the collision event must be scan freshness only (2026-10-20, lead)

Landed from `codex/cx-priv-history2-20261021` (`r1p-final/PRIVACY-HISTORY-REAL-20261021.md`).
The D91 ruling was wrong as stated. An event covering all repeated reads in
the whole run has mass one, since an admissible adversary may query the same
input twice, and the compiled counterexample shows this. Adversarial repeats
are not collisions. The job also proved the arithmetic κ(q) = 6q²/2^256 below
the target for q ≤ 2^65.

Corrected ruling: the excluded event is scan freshness failure only, where
some input of the honest real-side scan query was already in the oracle table
when the scan issued it, whether queried by the adversary, the prover, or an
earlier scan step. Its mass is bounded through what makes the scan inputs
unpredictable: fresh oracle outputs or fresh prover randomness in the scan
state. The bound is about (scan queries) × q / 2^k, with k the min-entropy of
that state, charged once. Adversarial repeats on other inputs cost nothing.

## D94 — real-side history law discharged by scan freshness (2026-10-20, lead)

Landed from `codex/cx-priv-history3-20261021` (`r1p-final/PRIVACY-HISTORY-FRESH-20261021.md`).
`PrivacyR1FinalProtocolHistoryReal` removes `real_model_history_law`. The
real failure events are fixed to the actual parser. The scan-input identities
are traced, the scan state is proved to carry a conservative 190 bits of
entropy, and E_fresh (a scan input already in the table) is bounded by a
union bound: mass ≤ 128q/2^190, with q = 8·n1 + 1 the instance's honest scan
count, not an adversary parameter. Internally a broader honest lazy-collision
budget is proved to fit inside that allowance; the note states this as an
inequality of budgets, not an equality of events. Error:
modelError + 16/2^486 + 128q/2^190 ≤ 2^-109 + 2^-137 + 2^-454 + 2^-118 < 2^-100.
The current release privacy theorem is
`PrivacyR1FinalProtocolHistoryReal`. The remaining premises are source
execution joins (the ModelExecutionJoins and the builder/SourceIdentification
rows of D89). 10 modules, 41 audits, zero swap.

## D95 — prover commitment part 4: oracle-parametric refinement, sampler open (2026-10-20, lead)

Landed from `codex/cx-prover-commit4-20261021` (`r1p-final/PROVER-COMMIT4-20261021.md`).
The D92 oracle route works. Eleven focused Kani checks pass with a shared
memoised symbolic oracle, including the `HOST_HASH` function-pointer route
and the packed-leaf, reserved-salt and expander limb transitions. The
callback refinement is proved in Lean parametric in the byte oracle and
specialised to the ROM; 14 theorems, env J 8157, standard axioms. Shipped
additions (cfg-gated, additions only in `state_only_{entropy,hiding}.rs`) were
rebuilt and all three frozen ELFs are byte-identical. A checked theorem shows
that zero-filling the unused H1 tape coordinates is not an equal-fibre
adapter. Still open: both full 16-try sampler comparisons timed out at 600 s
without a verdict (not rerun); a valid completion or quotient-tape
construction; sampler composition; and the caller/carrier/exhaustion/count
joins. All nine checklist rows stay open.

## D96 — builder refinement part 4: builder soundness removed at the canonical instance (2026-10-20, lead)

Landed from `codex/cx-builder-ref4-20261021` (`r1p-final/BUILDER-REFINEMENT-20261021.md`).
`PrivacyR1FinalProtocolBuilder` removes builder soundness and `hpub` at the
canonical extracted builder instance. Proved: the shipped semantic public
projections (extracted), lossless record reconstruction, field-normalised
record mappings, and conditional `SourceIdentification` assembly through a
single `RustRuntimeJoin`. 27 standard-axiom theorems and 81 Kani component
verdicts, including the full empty-root helper certificate. No shipped file
changed. Still open: successful-source admission, complete bank/glue equality
(the bank extraction leaves five unsupported std externals and was rejected
as a certificate), and real checker/retry execution coupling;
`RustRuntimeJoin` is not yet inhabited for the shipped prover.

Finding: the compile path accepts a non-canonical recipient-owner limb
(an M31 storage word ≥ p). The handoff now uses field-trace equality, not
raw canonicality. Lead action: check that the frozen verifier and Pool reject,
or canonicalise, non-canonical public limbs, so that one statement cannot
have two accepted encodings (nullifier or recipient malleability). A targeted
job is open.

## D97 — encoding uniqueness: no aliasing in the frozen verifier or Pool (2026-10-21, lead)

Resolves the D96 follow-up. Landed from `codex/cx-encoding-inj-20261021`
(`100bit-spend-path-20261013/design/ENCODING-UNIQUENESS-20261021.md`, moved by
the lead from a stray root `design/`; harness in `tools/encoding-uniqueness/`).
Every M31/QM31 public and checkpoint limb the frozen verifier and Pool decode
rejects words ≥ p. Raw addresses and integer seeds keep their full values,
and the nullifier-marker derivation rejects non-canonical encodings before
hashing, so one statement has exactly one accepted encoding and one marker
PDA. The Lean soundness and privacy statements are over field values. D96's
private owner-word normalisation is prover-internal and creates no public
parser alias. Native tests against frozen source: 7/7, including the saved
tx1/tx2 proofs and checksum-repaired checkpoint mutations (20.6 s, 500 MB,
zero swap). No shipped change, 0 CU. Optional: an off-chain witness
canonicality check in the prover, which is not needed for soundness.

## D98 — prover commitment part 5: sampler and tape quotient proved; premise shape wrong (2026-10-21, lead)

Landed from `codex/cx-prover-commit5-20261021` (`r1p-final/PROVER-COMMIT5-20261021.md`).
Both single-try Kani comparisons pass with the shared memoised oracle, and
Lean proves the extracted reference sampler equals 16 compositions of its
extracted step, so the timed-out 16-try harness is replaced. Proved: the H1
tape quotient with a measure-preserving completion, exact measure transport,
full honest-view invariance, partial-decoder fibre/failure transport, and the
counter subslots from the existing count/block premises. Env J 8187, 44
audits, standard axioms, zero swap. Additions only in
`state_only_{entropy,hiding}.rs` (cfg-gated); all three frozen ELFs rebuilt
byte-identical.

All nine checklist rows stay open, because the checklist premise asks for an
equal-fibre map on full tapes, and a checked theorem shows that every
deterministic quotient representative misses full tapes. Lead ruling: the
premise has the wrong shape. Restate it as the quotient law (equal fibres on
the H1 quotient, plus the proved measure-preserving completion), which the
full-tape form implies and is therefore strictly weaker, and show the
privacy endpoint still follows. Then close the concrete source quotient
decoder/carrier law, commitment-observable transport and the
caller/count/exhaustion instance.
## Builder refinement continuation 5 — composed release endpoint and std-model bank port (2026-10-21, worker)

Branch `codex/cx-builder-ref5-20261021`, base `b89c4bae8`.
`PrivacyR1FinalRelease.privacy_R1_release` composes D94's fixed-event history
reduction with D96's canonical-builder/public reduction. Its conclusion is
D94's error bound including freshness and <2^-100; builder soundness and
hpub are removed at the canonical instance. Exact signature comparisons and
all remaining premise owners are in `r1p-final/PRIVACY-RELEASE-20261021.md`.

Five proved std models now replace the rejected bank extraction's externals;
the adapted complete merged_banks definition compiles and audits to standard
axioms. Additional results cover finite Vec map collection, bounded array
construction, shift-count port semantics, actual bank dispatch predicates,
and the actual extracted digest8-to-canonical bridge. Eight new modules,
25 theorems, env J 9226–9247 (including retained failures), final current-object
and dependency audit in `r1p-final/release-final-audit.json`; every successful
attempt has zero swaps. No shipped crate source changed.

Part 1 remains open. A new isolated extraction of actual records (all three
copy crates included) still fails at the selected-sibling borrow,
pair_forest_copy_builder.rs:230 / InterpAbs.ml:1688. Charon 0, Aeneas 2;
full source/tool pins and capped resource receipts are in
`r1p-final/records-focused-evidence.json`. This was not a whole-compiler rerun
or a memory failure. The std blocker is cleared, but whole-bank refinement,
successful-source admission, a concrete shipped RustRuntimeJoin and real
checker/retry execution coupling are not proved. The canonical release
composition is conditional on the same fixed-event execution joins as D94.

## D99 — one release privacy theorem (2026-10-21, lead)

Reviewed `codex/cx-builder-ref5-20261021`; the worker's entry is above.
`PrivacyR1FinalRelease.privacy_R1_release` (D94 + D96 at the canonical
instance, error including freshness < 2^-100, signature-audited against both)
is now the single privacy reference, with the owner table in
`r1p-final/PRIVACY-RELEASE-20261021.md`. Lead route for the remaining
`records` blocker (Aeneas fails at `pair_forest_copy_builder.rs:230`): use the
P6 pattern. D90 already proved all 20 `records` fields equal to an owned
reference by Kani, and that reference translates, so cite Kani shipped =
reference and Lean on the extracted reference, instead of extracting the
shipped function.

## D100 — prover commitment part 6: quotient-form privacy endpoint (2026-10-21, lead)

Landed from `codex/cx-prover-commit6-20261021` (`r1p-final/PROVER-COMMIT6-20261021.md`).
Per D98, `PrivacyR1FinalProtocolQuotient` replaces the full-tape equal-fibre
premise with the H1 quotient law; the old premise is proved to imply the new
one (strictly weaker), and the release conclusion is unchanged. Also proved:
full constructed commitment-observable transport, sequential decoder
quotient fibres with derived cF, sampled field carriers, successful input,
and model count/budget bounds. Final audit J8239: 52 standard-axiom results,
zero swap; all 491 ELF input hashes unchanged. Open: the shipped caller
identity (the aggregate Aeneas obstruction persists), exact RExh cursor
classification, and universal read coverage. No checklist row is closed yet.
Note: this endpoint is built on `PrivacyR1FinalProtocolHistoryReal`, while
builder part 6 builds on `PrivacyR1FinalRelease`; the two will be merged
into one release endpoint once both land.

## D101 — builder refinement part 6: records via P6 route, bank complete (2026-10-21, lead)

Landed from `codex/cx-builder-ref6-20261021` (`r1p-final/BUILDER-CONT6-20261021.md`).
Per D99, `records` is closed by the P6 route: total refinement of all 20 owned
reference fields, composed with D90's Kani shipped = reference verdicts as a
named P6 certificate. Also proved: actual common-validator refinement,
complete bank materialisation (derived 57-block size), and checked merge
equivalence. `PrivacyR1FinalReleaseSource` is the conditional source release
endpoint with the remaining joins explicit. 23 modules, 74 standard-axiom
audits, zero swap; no shipped change. Open: Aeneas reaches an unsupported
higher-ranked lifetime constraint in `derive_nullifier_with`, which blocks
full semantic admission; canonical Parts-content/column correspondence; the
shipped `RustRuntimeJoin` inhabitant; and real checker/retry coupling. Next:
P6 route for `derive_nullifier_with` too (Kani shipped = owned reference,
where the reference avoids the HRTB closure).

## D102 — builder refinement part 7: nullifier via P6 route (2026-10-21, lead)

Landed from `codex/cx-builder-ref7-20261021` (`r1p-final/BUILDER-CONT7-20261021.md`).
`derive_nullifier_with` is closed by the P6 route: an owned callback reference
without the HRTB closure extracts, and four Kani checks with the shared
memoised oracle and the verified raw-word contract prove shipped = reference
(cfg-gated module at the end of `spend.rs`; all three frozen ELFs rebuilt,
SHA-256 and byte comparison equal). Also proved: canonical merge, the Parts
component column handoff, actual Vec column materialisation and bank
composition, and conditional Parts/bank/column correspondence. 7 modules,
20 standard-axiom audits, zero swap. Next blocker: Aeneas hits a shared-borrow
internal error in the validated-tree `append_one` carry loop; same P6 route
next. `PrivacyR1FinalReleaseSource2` has an empty signature diff (no weakening
claimed). Open: complete semantic admission, primitive Parts-content
correspondence, the shipped RustRuntimeJoin, and checker/retry coupling.

## D103 — builder refinement part 8: carry loop passed; zeroisation destructor next (2026-10-21, lead)

Landed from `codex/cx-builder-ref8-20261021` (`r1p-final/BUILDER-CONT8-20261021.md`).
The `append_one` carry loop is closed by the P6 route: a projected carry-step
Kani check (368 checks), the extracted carry transition with its stopping
and frontier invariants, twelve primitive path/aux writer identities, and
the actual withdrawal auxiliary Parts content. The cfg-gated tail module is in
`incremental_merkle.rs`; all three frozen ELFs were rebuilt byte-identical. 7
modules, 26 standard-axiom audits, zero swap. `PrivacyR1FinalReleaseSource3`
keeps every premise (signatures audited). Next blocker: the forest
extraction reaches the volatile zeroisation destructor at
`state_only_trace.rs:90` (`&raw mut`, unsupported by Aeneas). Lead route:
zeroisation writes only the memory of the value being dropped and changes no
output. Treat that `Drop` as an opaque, excluded declaration with a proved
specification: a Kani harness shows it writes only within the dropped
value's bytes and returns unit, so nothing observable is lost. The model then
treats drop as a no-op on outputs.

## D104 — builder refinement part 9: Parts content complete (2026-10-21, lead)

Landed from `codex/cx-builder-ref9-20261021` (`r1p-final/BUILDER-CONT9-20261021.md`).
Proved: full actual Parts content and bank/column correspondence, the actual
occupancy inverse, and 46 primitive extraction identities. The zeroising
`Drop` is excluded by an exact opacity flag (metadata audited), and its
observation rule is proved. The projected volatile-store contract and bounded
destructor behaviour pass Kani, and forest reference translation now
succeeds. `PrivacyR1FinalReleaseSource4`: 16 modules, 129 standard-axiom
audits, zero swap; no premise deleted. No shipped change. Open: universal
destructor correspondence (whole-frame Kani reached the 6 GiB review point
and was stopped, per AGENTS.md); forest admission, with 24 unsupported
externals and timed-out validator comparisons; the shipped runtime
inhabitant; and checker/retry coupling.

## D105 — one privacy headline (2026-10-21, lead)

Landed from `codex/cx-priv-headline-20261021`.
`R1Z.PrivacyR1Headline.privacy_headline` composes the quotient line (D94 →
D100) with the builder line (D99 → ReleaseSource3) through a common builder
contract, with proved adapters for the abstract protocol, the canonical
builder and the source runtime join; there is no tape-carrier obstruction.
Its signature is audited against all six predecessors. Exact error:
ε = M·qmax/2^255 + M²/2^255 + εexh + 8·4096/((2^31−1)^4−1) + 16/2^486 + 128(M+1)/2^190
≤ 2^-109 + 2^-137 + 2^-454 + 128(M+1)/2^190 < 2^-100, with M = 8·n1 ≤ 2^25.
The numerical part needs no source hypothesis. Focused compile (env J 9500):
exit 0, 5.82 s, 4.13 GB, zero swap, standard axioms. `r1p-final/PRIVACY-HEADLINE-20261021.md`
is now the single privacy status reference (statement, plain-English premise
table with owners, audit). Remaining: source builder/runtime correspondence,
the commitment law, real/ideal execution joins and the release boundaries.
Builder part 10 and prover part 7 will be folded in when they land.

## D106 — privacy accounting premises discharged at the protocol instance (2026-10-21, lead)

Landed from `codex/cx-priv-acct-20261021` (appended to `r1p-final/PRIVACY-HEADLINE-20261021.md`).
`PrivacyR1HeadlineAcct.privacy_headline_acct` specialises the headline to the
protocol's values (L₁, L₂ = 4096 from `ProverCommitSourceDecoder`, the block
budgets, and the concrete M31 tower basis; cF stays universal because it
appears only in the untouched fibre premise) and removes: `hB` (the concrete
tower packing field laws), `R_commit_counter₁/₂` (strict < 2^64),
`R_commit_stream₁/₂` (16L ≤ 8E), `R_commit_cell_count`, `R_commit_blocks₁/₂`,
`R_wire_coin_carrier` (identity equivalence at the protocol base) and the four
Fintype/Nonempty sample-carrier instances. None was false at those values.
Env J 9704, 9707, 9712, standard axioms, zero swap. This is the current
privacy headline. Remaining: quotient fibres, exhaustion, builder premises,
batch/log, and the two execution joins.

## D107 — builder refinement part 10 (2026-10-21, lead)

Landed from `codex/cx-builder-ref10-20261021` (`r1p-final/BUILDER-CONT10-20261021.md`):
per-store and per-column byte-frame composition for the zeroising destructor
at arbitrary lengths; proved Lean models for all 24 forest std externals;
projected validator Kani checks with a symbolic loop induction, and
successful-validator frontier acceptance. `PrivacyR1FinalReleaseSource5` keeps
every premise. 8 modules, 52 audits, zero swap; no shipped change. Open: the
actual destructor pointer/iterator correspondence; full forest semantic
admission (the aggregate port hits callback-interface type mismatches); the
shipped `RustRuntimeJoin` inhabitant; checker/retry coupling. The last two
are the prover-side execution join, the privacy analogue of the
verifier-equals-dV join on soundness. One more pass goes to forest admission,
which is still a model step.

## D108 — wire batch/log premises: free constructor parameters (2026-10-21, lead)

Landed from `codex/cx-priv-wirelog-20261021` (`r1p-final/WIRELOG-20261021.md`).
`R_wire_D80_batches` and `R_wire_D80_ordered_log` cannot be deleted at the
current instance: its constructors take `log`, `fib` and `opens` as
independent parameters. Compiled counterexamples: empty openings break root
coverage, and an empty log with one root opening breaks the ordered-log
equation. Lead ruling: the same pattern as D85 and the soundness free-d
cases. Specialise `log`, `fib` and `opens` to the protocol's own D88 encoding
(the logical transcript encoding and phase leaves of PhaseProtocolInstanceBin),
then prove both premises there. The Rust serialisation equalling that
encoding stays a source join. Env J 9721, standard axioms, zero swap.

## D109 — builder refinement part 11; builder track paused (2026-10-21, lead)

Landed from `codex/cx-builder-ref11-20261021` (`r1p-final/BUILDER-CONT11-20261021.md`).
State-preserving forest callback adapters are proved, the aggregate forest
callback port now compiles, and forest selection and destructor cursor frames
are proved; inner/outer iterator Kani projections pass. 3 modules, 15
audits, zero swap; no shipped change. Full semantic admission and the
universal shipped-destructor correspondence stay open, and `RustRuntimeJoin`
and checker/retry coupling remain named premises. The builder's env-J
attempt range (9200–9399) is exhausted. Lead decision: pause the builder
track here after eleven passes. What remains is mostly the prover-side
execution join, and it resumes with a fresh attempt allocation when the user
reviews the plan.

## D110 — prover commitment part 7: one caller law (2026-10-21, lead)

Landed from `codex/cx-prover-commit7-20261021` (`r1p-final/PROVER-COMMIT7-20261021.md`).
Exact consuming-cursor exhaustion classification is proved, and quotient
failures are identified with the two wordsE exhaustion events. Both shipped
scalar callers are Kani-verified against the owned reference with verified
next-word callees (the shared memoised oracle, cfg(kani) only), and the
reference is extracted with its finite sixteen-step loop semantics proved.
`PrivacyR1FinalProtocolCaller` derives the fibre, exhaustion and budget
premises from one explicit `CallerLaw`, so the shipped-prover side of
those rows is now a single named caller refinement. Final J8266: 23
standard-axiom checks; all three frozen ELFs rebuilt byte-identical (shipped
edits are cfg(kani)/cfg(aeneas_ref) modules only, gated in `lib.rs`). Open:
full caller transport and universal read coverage. The scalar-summary,
four-coordinate and balancing comparisons hit 600 s timeouts and were not
rerun. All nine source checklist rows stay open. This endpoint builds on the
Quotient line; it should be folded into the D106 privacy headline.

## D111 — wire batch and ordered-log premises discharged (2026-10-21, lead)

Landed from `codex/cx-priv-wirelog2-20261021` (`r1p-final/WIRELOG-20261021.md`).
Per D108, `PrivacyR1HeadlineWire2.privacy_headline_wire2` (built on D106's
`PrivacyR1HeadlineAcct`) fixes the S2 transport, the logical log, the fibres
and the openings to the protocol's own encoding (logical opening batches and
disclosed leaf encoding are constructed), proves `R_wire_D80_batches` and
`R_wire_D80_ordered_log` symbolically, and removes both (deletion-only diff
after the specialisation). Env J 9740/9741, standard axioms, zero swap. The
residual is one named source join, `PhaseWireLog2Bin.RustSerializationJoin`:
Rust's complete ordered serialisation equals that logical encoding, including
the finite-set ordering and batch split. Current privacy headline:
`PrivacyR1HeadlineWire2.privacy_headline_wire2`. D110's caller law is on a
sibling line and still needs folding in.

## D112 — privacy headline v2 (2026-10-21, lead)

Landed from `codex/cx-priv-headline2-20261021` (v2 section of
`r1p-final/PRIVACY-HEADLINE-20261021.md`). `PrivacyR1HeadlineV2.privacy_headline_v2`
composes D111 (wire premises discharged, built on D106's accounting) with
D110's caller law, keeping ε < 2^-100. `privacy_headline_v2_fibres` is kept
as an alternative endpoint: the aggregate fibre/exhaustion premises do not
imply CallerLaw's pointwise decoder partition, so neither form is strictly
weaker and both stay available; the report gives the obstruction. Env J
9512, standard axioms, zero swap (9510 and 9511 failed and were fixed by source
changes). These two are the privacy headline. Remaining: the shipped caller
and builder refinements, the Rust serialisation identity, the real
checker/retry and ideal execution joins, and simulator implementation.

## D113 — prover commitment part 8 (2026-10-21, lead)

Landed from `codex/cx-prover-commit8-20261021` (`r1p-final/PROVER-COMMIT8-20261021.md`).
The three timed-out comparisons are now split into symbolic steps: a
scalar-step contract, four-coordinate trace checks and balancing-row checks,
each with a Lean induction. Five new Kani targets pass. Also proved: the
independence of the caller premises, and universal reference expander
support. J8280: 27 standard-axiom audits, zero swap; the shipped edits are in
the cfg(kani)/cfg(aeneas_ref) modules only, and all three frozen ELFs are
byte-identical. Open: the full shipped `CallerLaw` (the outer caller
transport) and universal shipped read coverage. The narrower owned-balancing
reference produces clean LLBC but hits an Aeneas internal error at the loop
boundary (`Not_found` in `InterpReduceCollapse.collapse_ctx_following_sequence`).
Next: reshape that reference loop (structural recursion over a fixed-size
array, or an explicit fold) to avoid the collapse path, and keep Kani's
shipped = reference.

## D114 — simulator cost, first pass (2026-10-21, lead)

Landed from `codex/cx-sim-cost-20261021` (`r1p-final/SIM-COST-20261021.md`):
an abstract cost writer with stage composition, exact cost erasure for
programmed-oracle replay, simulator-stage composition, and a bounded sampling
fallback (an expected-cost/truncation model for rejection sampling).
`PrivacyR1HeadlineV2Sim` keeps every V2 premise and conclusion and adds exact
ideal-game equality and a degree-one cost bound, under explicit preparation and
size contracts. 8 modules, 31 audits, zero swap. Open: a compiled
counterexample shows that unrestricted auxiliary `outputs` rule out a uniform
byte-cost bound at the generic signature. That is the free-parameter pattern
again, so pass 2 fixes `outputs` and the field/view stages to the protocol
instance (as D106/D111 did), then proves the size and preparation contracts
there.

## D115 — prover commitment part 9: balancing loops extracted (2026-10-21, lead)

Landed from `codex/cx-prover-commit9-20261021` (`r1p-final/PROVER-COMMIT9-20261021.md`).
Reshaping the owned balancing references into row recursion gets past the
Aeneas collapse error: both translate, Lean proves ascending-fold
equivalence for both complete owned balancing callers, and both Kani row
comparisons pass. J8288: 40 standard-axiom audits, zero swap; the shipped
change is in the cfg(kani)/cfg(aeneas_ref) reference module only, and all
three frozen ELFs are byte-identical. `CallerLaw` is not discharged, because
D112's headline quantifies over an arbitrary decoder. Same pattern as D108
and D114: part 10 fixes the decoder to the concrete shipped decoder (with its
execution transport), then proves CallerLaw and read coverage there.

## D116 — simulator cost pass 2: bound must be in adversary input length (2026-10-21, lead)

Landed from `codex/cx-sim-cost2-20261021` (`r1p-final/SIM-COST-20261021.md`).
Proved: the protocol preparation table length, programmed-key encoding bounds,
disclosed leaf widths 480/128/128 bytes, batch truncation cost bounds, and
explicit sampling-error arithmetic (the envelope plus truncation mass stays
< 2^-100). Obstruction (compiled): fixing the protocol outputs does not bound
the adversary's query lengths, so a cost bound uniform in the query count q
is false, and replaying a programmed table costs time proportional to the
query bytes. Lead ruling: that is the wrong efficiency notion. A ZK
simulator is efficient relative to the adversary, so the bound should be
poly(q + Σ|query bytes|), polynomial in the adversary's own query input
length (its running time). Pass 3 states and proves the cost in that form.
5 modules, 31 audits, zero swap; three memory-cap failures were replaced by
changed symbolic proofs, with caps unchanged.

## D117 — simulator cost pass 3: relative replay cost and sampling coupling (2026-10-21, lead)

Landed from `codex/cx-sim-cost3-20261021` (`r1p-final/SIM-COST3-20261021.md`).
Following D116, programmed replay cost is proved ≤ c·(n+1), with n the
adversary's query input length, and the protocol table contracts are
discharged. Also proved: lazy-ROM source laws, an adaptive lazy-oracle
coupling to uniform finite tables, a bounded M31 sampling law from uniform
binary words, and binary coupling for all eight protocol tapes (≤ 417,792
M31 samples, ≤ 3,342,336 draws, truncation mass ≤ 2^-120).
`PrivacyR1HeadlineV2SimProto` keeps every privacy premise and the < 2^-100
conclusion, and adds the relative cost conclusion, conditional on the
retained `sim_preparation`. Open: concrete field/preparation costs, lazy-cache
byte work and the whole-experiment source join; a compiled metadata example
shows the remaining limit on a uniform bound. 10 modules, 57 audits, zero swap.

## D118 — prover commitment part 10: fixed decoder, CallerLaw still open (2026-10-21, lead)

Landed from `codex/cx-prover-commit10-20261021` (`r1p-final/PROVER-COMMIT10-20261021.md`).
Per D115, the decoder is fixed to the operational reference decoder composed
from the extracted, Kani-matched references, and the headline is specialised
to it. Also proved: extracted owned collection proofs, finite block backend
counter correspondence, finite stream cursor/read bounds, and accepted-word
refinement. J8326: 41 standard-axiom audits, zero swap; the shipped change is
only in the cfg-gated reference module, and all three frozen ELFs are
byte-identical. `CallerLaw` is retained (empty deletion diff). Remaining:
cache/byte-load correspondence with `wordsE`, complete shipped outer-caller
transport, and all-family shipped read coverage. The nine-block Kani ROM is
proved insufficient for whole-array certification. These are the prover-side
execution join, so the prover track pauses here after ten parts.

## D119 — simulator cost pass 4; track paused (2026-10-21, lead)

Landed from `codex/cx-sim-cost4-20261021` (`r1p-final/SIM-COST3-20261021.md`):
an explicit lazy-cache implementation with exact erasure; an unconditional
protocol cache byte-work bound C·(n+1)² relative to the adversary's query
input length, with a matching fixed-preparation source law; and
certification of the M31/QM31 arithmetic batch stages under the existing
tariffs and the 417,792-coordinate bound. 4 modules, 20 theorems, standard
axioms, zero swap. `sim_preparation` stays open: operation counts for the full
preparation formulas, actual WideExact arithmetic, predicate/retry and
encoding composition, callback certificates, and the whole-experiment source
join. This env-J attempt range is exhausted, so the track pauses until a new
range is allocated.

## D120 — CallerLaw discharged at the fixed decoder (2026-10-21, lead)

Landed from `codex/cx-prover-commit11-20261021` (`r1p-final/PROVER-COMMIT11-20261021.md`).
Byte-load and finite oracle cache correspondence with `wordsE` are proved,
bounded scalar windows are composed over one retained global oracle, and
`CallerLaw` is derived for the fixed operational reference decoder (the D118
specialisation composed from the Kani-matched extracted references).
`privacy_headline_owned_closed` (`docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineOwnedClosed.lean`) removes
`R_commit_caller` with a deletion-only diff (the lead checked it). J8355: 32
standard-axiom audits, zero swap; no production change. This is the current
privacy headline. Open: shipped entry-point/outer-caller transport, i.e. that
the shipped prover entry calls these references in this order (the isolated
scalar-contract check timed out at 600 s even with all three verified summaries
active), and all-family callback coverage.

## D121 — prover commitment part 12 (2026-10-21, lead)

Landed from `codex/cx-prover-commit12-20261021` (`r1p-final/PROVER-COMMIT12-20261021.md`).
Proved: both one-iteration Kani checks of the shipped scalar loops pass
against the verified next-word summaries; Lean proves the sixteen-try
schedules and conditional state transport; the transcript, binary-parent and
literal 17-call query-prefix checks pass. J8363: 13 standard-axiom audits,
zero swap; no production change. No premise is removed. A checked
counterexample shows the builder premise cannot hold for every currently
permitted `input` (the free-parameter pattern again: fix `input` to the
protocol's admitted input domain), and the direct shipped extraction pulls in
`core::fmt::Formatter` (as in the checkpoint cone: stub the panic path after
proving it unreachable). Open: shipped outer execution transport and
all-family shared-oracle coverage.

## D122 — builder premise discharged on the canonical admitted domain (2026-10-21, lead)

Landed from `codex/cx-prover-commit13-20261021` (`r1p-final/PROVER-COMMIT13-20261021.md`).
Per D121, the endpoint is specialised to D96's canonical admitted spend inputs,
and `privacy_headline_admitted` (`docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitAdmittedEndpoint.lean`) removes `builder_premises` with a
deletion-only diff after the specialisation (checked by the lead). Also
proved, by 20 focused Kani checks: shipped stream-conversion safety with the
formatter stubbed unreachable, both complete scalar result/state laws,
query-caller result and retained-state transport around the sampler cut, and
the seed and outer binding boundaries. J8372, standard axioms. This is the
current privacy headline. Remaining premises: the two execution joins
(`R_wire_builder_checker_D75_retry` and the ideal-side `G_sim_R_wire`), i.e.
outer execution transport and all-family shared-oracle coverage. Blocker: the
outer material loop (source lines 471–489) fails at Aeneas's loop-context join.
Next: an owned indexed material-loop reference with per-iteration P6 equality.

## D123 — prover commitment part 14: material loop (2026-10-21, lead)

Landed from `codex/cx-prover-commit14-20261021` (`r1p-final/PROVER-COMMIT14-20261021.md`).
The owned material schedule is extracted and its finite recursions proved;
deterministic material oracle support and the bridge from scalar windows to
the retained global cursor are proved; all nine M31 material-cell cases pass
Kani (success, exhaustion, and prefixes of length ≤ 2). J8389: 33 standard-axiom
audits, zero swap; no production change. No premise is removed. A
counterexample shows that unrestricted `observer_program` replacement cannot
supply history equality, so the real execution join needs the observer fixed
to the protocol's. Open: arbitrary-prefix/QM31 source transport,
returned-material assembly, the complete builder/checker/retry history, and
all-family coverage; `G_sim_R_wire` stays named.

## D124 — serialisation-order mismatch; the fixed-observer endpoint is model-only (2026-10-21, lead)

Landed from `codex/cx-ser-join-20261021` (`r1p-final/SER-JOIN-20261021.md`)
and `codex/cx-prover-commit15-20261021` (`r1p-final/PROVER-COMMIT15-20261021.md`).

1. **Modelling error in D111.** The shipped prover splits the ordered q22
   query array into its batches (10 + 12) and then sorts each batch. D111's
   logical encoding splits `Finset.toList` of the query set and discards
   order. `SerJoinOrderObstruction.cannot_match_both` proves that no single
   encoding agrees with both of two valid query orders with the same set, and
   the shipped sampler accepts both. This is not a leak (the order is
   derived from the public transcript), but the privacy model must keep the
   ordered q22, as the soundness model dV_frozen2 already does. D111's wire
   discharge has to be redone over ordered queries. Also,
   `RustSerializationJoin` was never a binder of the headline; it was only a
   documented residual, which is a bookkeeping gap.
2. **Model-only endpoint.** Specialising `observer_program` to the
   constructed source's own observer makes both execution joins identities
   (the model compared with itself), so they were deleted. The worker states
   this correctly: it proves nothing about the Rust prover.
   `privacy_headline_admitted` at that specialisation is a **model-level**
   theorem. Lead ruling: the deployed privacy claim must carry one explicit
   premise, `RustProverRefinement`, meaning the real shipped prover's whole run
   (builder, checker, retry, serialisation and observer) equals the constructed
   source outside the named bad event. Nothing may be described as deployed
   privacy without it. J8399/J8500, standard axioms, zero swap.

## D125 — deployed privacy endpoint with an explicit Rust refinement premise (2026-10-21, lead)

Landed from `codex/cx-prover-commit16-20261021` (`r1p-final/PROVER-COMMIT16-20261021.md`).
Per D124: `PrivacyR1HeadlineDeployed` (`lean/R1Z/PrivacyR1HeadlineDeployed.lean`)
states deployed privacy with one explicit premise, `RustProverRefinement`. It
says the given implementation's whole real run, and its ideal run, are each
joined (`WholeRunJoin`) to the constructed source's, including the observer
view, the ordered observer history and the decision, outside only the fixed
model bad events `realBad` / `selectedBad`. It cannot be emptied by
specialisation, and the privacy bound is unchanged. The model now keeps
ordered queries: ordered 10 + 12 batches, public log re-encoding and
adaptive-observer transport are proved, which repairs the D111 order mismatch.
Also: universal extracted M31/QM31 prefix bridges, returned-material assembly
support, and four section-wise codec Kani checks. J8640: 32 standard-axiom
audits, zero swap. **Current privacy headlines:** the model-level
`privacy_headline_admitted`, and the deployed `PrivacyR1HeadlineDeployed`,
conditional on RustProverRefinement. Open (the content of that premise): the
concrete runtime refinement, exact serialisation traversal, and
borrowed-loop / outer-assembly identification. Three ordered-Vec Kani attempts
timed out and were excluded.

## D126 — prover commitment part 17; the Rust experiment must be made concrete (2026-10-21, lead)

Landed from `codex/cx-prover-commit17-20261021` (`r1p-final/PROVER-COMMIT17-20261021.md`):
ordered List and section composition of the serialiser; bounded serialiser
emission-cell and ordered-query-element Kani checks; borrowed-cell checks;
an extracted owned outer assembly with error-preserving Lean composition.
J8655, standard axioms, zero swap. `RustProverRefinement` stays open. A checked
countermodel shows it cannot be deleted while `rust : FSExperiments` is
unrestricted. That is the free-parameter pattern again, and it does not refute
the actual prover. Lead ruling: build `shippedProverExperiment : FSExperiments`
as a concrete Lean object from the extracted owned references and the
Kani-certified shipped = reference equalities (builder, checker, retry,
serialiser, material, scalar callers), with its randomness and history
adapter. Then prove both WholeRunJoins for `rust := shippedProverExperiment`.
The residual is then only the P6 toolchain boundary (the Kani/Aeneas
translation is trusted), which is already a named premise.

## D127 — prover commitment part 18; seed-guess term missing from the bad event (2026-10-21, lead)

Landed from `codex/cx-prover-commit18-20261021` (`r1p-final/PROVER-COMMIT18-20261021.md`):
a bounded attempt-entropy model with retained errors and draw state; entropy
failure transport under fixed bad events; bounded entropy symmetry with an
unchanged draw history; the simulator's one-coin transition (Kani,
owned-reference extraction and Lean); exact frame separation and finite-ROM
marginal uniformity. J8674: 33 standard-axiom audits, zero swap. No concrete
`shippedProverExperiment` yet; `RustProverRefinement` unchanged. Finding: the
shared-oracle component has a seed-guess gap of 2^-256 − 2^-512, which is more
than the query-scan-only allowance in `realBad`/`selectedBad`, so joint
history equality cannot follow from marginal uniformity under the current bad
event. Not an attack. Lead ruling: add an explicit seed-guess event (the
adversary queries the simulator's seed point) to the fixed bad events,
charged once at q·2^-256 for q oracle queries, and re-prove the privacy error
bound, which stays far below 2^-100. Also open: the full simulator extraction
(has_errors) and the timed-out entropy-exhaustion Kani check.

## D128 — seed-guess event added; joint history coupling (2026-10-21, lead)

Landed from `codex/cx-prover-commit19-20261021` (`r1p-final/PROVER-COMMIT19-20261021.md`).
Per D127: the global simulator seed query budget and seed-query exceptions are
added to the deployed refinement's fixed bad events, with containment and
transport from the old premise to the new one, and the revised privacy bound
stays < 2^-100. The bounded joint adaptive-history coupling is constructed,
including programmed lookup and shared-oracle fallback, which closes the gap
D127 found. Three entropy rejection checks pass, with the sixteen-draw Lean
induction; owned simulator helpers are extracted. J8704: 42 standard-axiom
audits, zero swap. Still open: the owned simulator's transcript/parser cone
hits Aeneas `Not_found`, the table-source Kani check timed out,
`shippedProverExperiment` is not yet constructed, and `RustProverRefinement`
stays explicit. **Pending check:** the job appended a cfg(any(kani,aeneas_ref))
module at the end of shipped `aspis-r1-cost-probe/src/sim.rs` (additions only,
no lines moved, excluded from production builds) without rebuilding the ELFs.
The next prover job must confirm all three frozen ELFs byte-identical as its
first stage.

## D129 — frozen ELF recheck at the research tip: all three match (2026-10-21, lead)

Clears the D128 pending check. `codex/cx-elf-recheck-20261021` (evidence
`100bit-spend-path-20261013/evidence/elf-recheck-20261021/RESULTS.md`) rebuilt
the three frozen programs from the research tip, including the cfg-gated
`sim.rs` addition. Default verifier `dfc2a91a…`, devnet `fb2fc048…` and Pool
`121f3e29…` all **MATCH** (SHA-256 and byte-for-byte cmp; the unstripped
linked ELFs also match). Capped builds, zero swap.

## D130 — simulator semantic cone extracted (2026-10-21, lead)

Landed from `codex/cx-prover-commit20-20261021` (`r1p-final/PROVER-COMMIT20-20261021.md`).
The Aeneas `Not_found` is isolated to `validate_record_fields`. An owned
validator, and the complete 25-row semantic cone, are extracted with no
external templates. Proved: finite validator and row schedules, table-write
semantics, per-entry table composition, and adaptive programmed-history
composition. Focused Kani checks and the semantic differential fixtures pass.
J8732: 21 standard-axiom audits, zero swap; no shipped change (D129 ELF
evidence stands). Open: the actual overwrite-flag Kani check timed out at
600 s; universal table/source transport; the later simulator traversal; and
uncapped nonzero-loop treatment. `shippedProverExperiment` and the
WholeRunJoins are not yet constructed.

## D131 — prover commitment part 21; nonzero-search ruling (2026-10-21, lead)

Landed from `codex/cx-prover-commit21-20261021` (`r1p-final/PROVER-COMMIT21-20261021.md`):
arbitrary-prefix table composition with a split per-entry gate (which
replaces the timed-out overwrite-flag check), universal owned-key transport,
generic opening-control extraction, and both differential fixtures over
complete ordered oracle histories and serialised traces. J8747: 24
standard-axiom audits, zero swap; no shipped change. Open: universal BTreeMap
transport, the concrete circle/sampler/TLS joins, and nonzero
termination/divergence, now localised to one shared oracle stream.
Lead ruling on divergence: the shipped loop draws until it gets a nonzero
value, so it terminates with probability 1 and has no cap. Model it as a
fuel-bounded loop with fuel k, a protocol constant fixed in the model. Runs
that finish within k draws are identical; runs that exhaust k are added to the
fixed bad events, charged at (1/p)^k per stream instance times the number of
instances, with p the field size (≈ 2^-31 per draw). Choose k so the total
charge is ≤ 2^-120, and re-prove the privacy bound stays < 2^-100.

## D132 — prover commitment part 22: fuel-bounded nonzero search (2026-10-21, lead)

Landed from `codex/cx-prover-commit22-20261021` (`r1p-final/PROVER-COMMIT22-20261021.md`).
Per D131: a five-draw nonzero model agrees with terminating source runs within
the fuel, and the shipped loop's Kani check passes. A fixed exhaustion charge
of ≤ 2^-120 per side is added to the bad events, the old events are proved
contained in the new ones, and the enlarged-event deployed privacy bound
stays < 2^-100. Also proved: universal Lean Std.TreeMap transport over finite
write schedules, and reuse of the concrete QM31 and circle sampler proofs,
fallbacks included. J8772: 42 standard-axiom audits, zero swap; no shipped
change. Open: the BTreeMap source gate was stopped near MemoryHigh, as
AGENTS.md requires; native TLS reaches the unsupported `pthread_key_create`,
so stub the thread-local accessor with a verified single-threaded contract;
adaptive fuel/history transport; and the caller/policy assembly.
`shippedProverExperiment` and the WholeRunJoins are not built yet. The
prover track's env-J range 8600–8799 is nearly used up (8773+ remain).

## D133 — prover commitment part 23; BTreeMap as a trusted std boundary (2026-10-21, lead)

Landed from `codex/cx-prover-commit23-20261021` (`r1p-final/PROVER-COMMIT23-20261021.md`):
single-thread TLS access semantics with a validated trace stub; adaptive fresh
fuel bounds with the exact marked-answer law; split map source gates and
write-schedule composition; the concrete rho/QM31 sampler policy and the
programmed TLS slot; the joint adaptive history law with supplied and memoised
draws. The TLS, one-entry lookup and iterator gates pass. J7486: 24
standard-axiom audits, zero swap; no shipped change. The split BTreeMap
insertion gate still approached MemoryHigh after two proof-shape changes and
was stopped, per AGENTS.md. Lead ruling: do not verify std's B-tree internals.
Put `std::collections::BTreeMap` (insert/get/iter as the prover uses them)
in the trusted std/allocation cone (S10 pass 4), with its documented
ordered-map semantics as the spec, i.e. the universal TreeMap model already
proved. Record it as an explicit named trust item next to rustc/P7, so it
is visible, not hidden. The single-thread assumption for TLS is recorded on
the same list.

## D134 — prover commitment part 24; coupling needs an independent fuel tape (2026-10-21, lead)

Landed from `codex/cx-prover-commit24-20261021` (`r1p-final/PROVER-COMMIT24-20261021.md`).
The trusted-std list is named (ordered map and single-thread TLS contracts,
per D133). Also proved: adaptive map caller transport, room in the source
search counters, and source-window freshness outside the seedGuess event.
J7499: 24 standard-axiom audits, zero swap. Two obstructions, both about the
proof construction, not about privacy:
(1) `runJoin_not_model_function`: the RunJoin's extra fuel tape cannot be any
deterministic function of the model coins and seed. Lead ruling: build the
coupling on the product space (model coins × an independent uniform fuel
tape), prove both marginals (the real run's coins are exactly that product,
and the model ignores the fuel except on the already-charged exhaustion
event), then derive the WholeRunJoin.
(2) The retained Aeneas packet for `sampler.add_small_base_p` has an iterator
ABI mismatch (`into_iter_back back`). Re-extract that function on its own
with the pinned kit, or use an owned reference with Kani shipped = reference,
and install unconditional gamma/ordinary/query policies from it.
`shippedProverExperiment` and the endpoint are not built yet.

## D135 — prover commitment part 25: product coupling built (2026-10-21, lead)

Landed from `codex/cx-prover-commit25-20261021` (`r1p-final/PROVER-COMMIT25-20261021.md`).
Per D134: the rejection-sampling coupling is built on independent product coins,
with a product RunJoin for the retained rejection component state, adaptive
rejection windows packed into the uniform source oracle, the finite-oracle
marginal, and adaptive observer-history transport. Also: the circle caller is
extracted with a total coordinate policy; total owned gamma/ordinary/rho
scalar policies are installed; circle discriminants are namespaced for
coherent imports; and the shipped add-small traversal is Kani-verified against
the indexed reference (which replaces the mismatched retained packet). J7583:
52 standard-axiom checks, zero swap; no shipped change. Open: the low-digit
arithmetic gates timed out (600/180 s), the concrete query/source composition,
`shippedProverExperiment`, both WholeRunJoins and the endpoint
specialisation.

## D136 — prover commitment part 26; CoinOracle is stateful (2026-10-21, lead)

Landed from `codex/cx-prover-commit26-20261021` (`r1p-final/PROVER-COMMIT26-20261021.md`):
low-digit arithmetic split into verified cells with a symbolic induction
(replacing the timed-out gates); the concrete query policy installed and
total, including first-stop; complete record validation transported into the
circle caller; the coupled finite oracle installed in the concrete digest
APIs. J7635: 40 standard-axiom checks, zero swap; no shipped change. Finding:
the native `CoinOracle` advances a `RefCell` cursor and can return different
answers for identical inputs, which makes it a coin tape, while the extracted
`Digest32` interface returns no updated state. A native counterexample and a
Lean determinism theorem show a stateless interpretation is invalid. Not a
privacy issue. Lead ruling: interpret CoinOracle as a state-passing coin tape
(cursor threaded explicitly), the same tape as the coin component of the D134
product coupling. Extend the extracted interface so each call returns
(digest, updated cursor, recording/collision effects), prove the extracted
calls preserve exactly those effects, then assemble shippedProverExperiment.

## D137 (lead, 2026-10-22 00:10): part 27 merged; coin tape effects proved, continuation port is the next obstruction

Merged `codex/cx-prover-commit27-20261021` (report
`r1p-final/PROVER-COMMIT27-20261021.md`). Proved: the extracted state-passing
CoinOracle calls preserve exactly their (digest, cursor, recording/collision)
effects, universally per call and by induction over adaptive call sequences;
the D134 product-coupling marginals hold with the explicit cursor (concrete
115-word tape); effectful semantic/circle/suffix caller skeletons. 34 axioms
reports, standard axioms only. Per-call RefCell Kani gates and the 115-word
read-address gate pass; monolithic 115-word checks timed out and are excluded.
No shipped file changed (D129 ELF evidence still applies).
Not established: the retained full walk/policy continuations still consume a
pure `Digest32` (`Machine → … → Result Bytes32`), so they cannot take the new
`Result (Bytes32 × Machine)` operation (J7673 installation probe). This is an
interface-composition obstruction, not a privacy counterexample.
`shippedProverExperiment`, both WholeRunJoins and the endpoint remain open;
`RustProverRefinement` stays explicit; zero premises removed.
Next (part 28): port the complete effectful continuation (replay reset, query
selection, native trace, retries, commitment programming, ordered
serialisation) to the state-passing operation, then the joins and endpoint.

## D138 (lead, 2026-10-22 01:30): part 28 merged; continuations ported, native walk loop is the next obstruction

Merged `codex/cx-prover-commit28-20261022` (report
`r1p-final/PROVER-COMMIT28-20261022.md`). Closed the D137 interface mismatch:
a generic monadic state lift, with kernel-checked source reconstruction, ports
the complete transcript continuations to the state-passing CoinOracle.
Composed the stateful semantic/circle/query/rho walk with ordered read
history, replay reset, product marginals and extracted initialisation.
35 axioms reports, standard axioms only, zero swap (J7831). No shipped change.
Obstruction: Aeneas cannot extract the native `sim::walk` borrowed semantic
loop (`sim.rs:165–177`, `for row in 0..25 { sem[row] = st.semantic(...)? }`;
InterpJoin.ml:2209). Next (part 29): the P6 route for that loop: an owned
reference loop, a per-iteration Kani shipped=reference check, a Lean induction
over the 25 rows connecting it to the bounded stateful row continuation, then
`shippedProverExperiment`, both WholeRunJoins and the endpoint.
`RustProverRefinement` stays explicit; zero premises removed.

## D139 (lead, 2026-10-22 05:10): part 29 merged; native caller gate times out, callee contract next

Merged `codex/cx-prover-commit29-20261022` (report
`r1p-final/PROVER-COMMIT29-20261022.md`). Added cfg(kani/aeneas_ref)-only
owned modules `fields20`/`semantic20` in `aspis-r1-cost-probe` (`r1_wire.rs`,
`sim.rs`); all three frozen ELFs rebuilt byte-identical (dfc2a91a…, fb2fc048…,
121f3e29…), 492 shipped files pinned (`frozen-elf-final-check.json`).
Proved for the owned reference: extracted iteration including record lookup,
finite-row induction over rows 0..24, and composition through both circle
points and the Transcript tail. Bounded field validation certified.
26 axioms reports, standard axioms only.
Obstruction: the native per-row Kani gate still times out at 600 s (rows 14
and 15, where field validation starts), because the caller gate expands the
whole callee. No counterexample. Next (part 30): a separately verified
native/owned contract for the semantic callee (field validation, rejection
state, ordered hash effects), used as a verified stub in the caller gate,
then the native-to-owned walk equality, `shippedProverExperiment`, the joins
and the endpoint. `RustProverRefinement` stays explicit; zero premises removed.

## D140 (lead, 2026-10-22): simulator cost pass 5, partial

Merged `codex/cx-sim-cost5-20261022` (report `r1p-final/SIM-COST5-20261022.md`).
Proved in the primitive-RAM cost model: WideExact addition 10 ticks,
multiplication 170, total inversion ≤ 85,065; materialised payload-array
addition ≤ 429,399,348 ticks; all 24 five-draw fuel selections ≤ 11,832
worst-case ticks, with exhaustion mass ≤ 2^-120 under the retained independent
tape. 38 standard-axiom audits, zero swap; no shipped change.
`sim_preparation` stays (empty deletion diff). Open: reference/mask/shift
costs, predicate/callback/encoding certificates, preparation composition. The
whole-experiment simulator source join is part 30's ideal `RunJoin`
interface, named in the report and not duplicated.

## D141 (lead, 2026-10-22 02:20): part 30 merged; native walk certified, outer owner next

Merged `codex/cx-prover-commit30-20261022` (report
`r1p-final/PROVER-COMMIT30-20261022.md`). Closed D139: the native semantic
callee (field validation, rejection state, ordered hash effects) is verified
on its own; all 25 per-row caller gates pass using that verified contract
(331 s total, largest peak 629 MB); the Lean range owner composes the native
loop with the stateful walk model. So the whole native `sim::walk` equals the
stateful model walk, at the Kani/P6 boundary. Standard axioms only; no shipped
change (part-29 ELF evidence reused).
Obstruction: Charon translates `sim::sim_e_ablated` (`sim.rs:396`) with
`has_errors=true` (five Iterator trait-clause mismatches: BTreeMap Iter and
IntoIter, Enumerate, ChunksExactMut, Zip), so the outer retry/publication
owner is not extracted. Two further named gaps from the report: no certified
owner converts the source outputs (proof bytes, programming tables, status)
into the `FSExperiments` real/ideal `ROMView` plus the observer's ordered
transcript; and the entropy model retains OS failure and zero-draw events,
which must stay explicit bad events, not be assumed away.
Next (part 31): owned references for the `sim_e_ablated` publication loops
certified against BTreeMap Iter/IntoIter per transition (conflict retention,
key order, early exits); the eight-attempt retry/publication owner; the
real-side `prove_masked_retrying_with` publication; then the source-to-
`FSExperiments` conversion. `RustProverRefinement` stays explicit.

## D142 (lead, 2026-10-22 02:25): simulator cost pass 6; ruling on callbacks

Merged `codex/cx-sim-cost6-20261022` (report `r1p-final/SIM-COST6-20261022.md`).
Proved: sparse WideExact shift suffix ≤ 85,439 ticks; the payload indexing and
array-addition representation bridge; exact outer `firstGood` retry control
8·C + 17 ticks. Standard axioms, zero swap (J8819–J8830); no shipped change.
Finding (`no_uniform_callback_tariff`): with the endpoint's current
quantifiers, the public-output callback and template/wire functions (frame,
payload, final, pubBytes, decoder, lookup) range over an arbitrary family, so
no numeric cost bound can hold (callback `bytes (C+1)` exceeds any C).
**Lead ruling (free-parameter pattern):** these are protocol functions, not
adversary inputs, so specialise them to the shipped R1 instance, the actual
encoders and decoder used by the frozen simulator/prover. This is the same
fix as earlier specialisations: a premise that is false for arbitrary
parameter values is restated at the protocol's actual values. It restricts
no adversary capability. The adversary's queries remain arbitrary, and cost
stays relative to their length. The report must show the before/after
quantifiers and confirm that no adversary-chosen input is among the fixed
functions. Next (pass 7): the concrete callback/wire instance; reference/mask
and terminal-read costs; the exact P_R1 predicate decision; composition into
`SimCostIdeal.Preparation` with numeric C; endpoint without `sim_preparation`.

## D143 (lead, 2026-10-22 02:30): simulator cost pass 7; rulings on pubBytes and observables

Merged `codex/cx-sim-cost7-20261022` (report `r1p-final/SIM-COST7-20261022.md`):
source inventory (22 pins) and the exact next interface; no Lean build, no
shipped change. Correction to D142: the composed wire already fixes frame,
payload, final, decoder and lookup; what remains quantified is `CommitHandle`,
`Aux`, `pubBytes` (in `template`) and `outputs`.

Lead rulings:
1. **pubBytes.** Do not invent an error value. The model statement's fields
   are typed in K, hence canonical. The obligation is that, for every model
   statement, the shipped `r0::Public::public_bytes` on its source image
   returns `Ok(pubBytes x)`; the Rust rejection branch is then provably
   unreachable from model statements. This is a proof obligation, not a
   choice.
2. **Observables (`Aux`/`outputs`).** The adversary's view is what the
   deployed system reveals: the public statement bytes, the submitted proof
   bytes, and the oracle's answers to its own queries. The simulator's
   programming table, attempt counts and timings are not published by the
   protocol. They are internal to the local prover/simulator, so `outputs`
   must be the projection onto exactly the published data, with a proof that
   nothing else is observable in `FSExperiments`. **Timing and other side
   channels are outside the privacy contract.** This is recorded as an explicit
   scope line, not silently excluded, and is flagged to the user.
3. This interface is the same source-to-`FSExperiments` conversion that
   privacy part 31 item (4) is building. Pass 8 waits for part 31's result so
   the conversion is built once.

## D144 (lead, 2026-10-22 02:50): part 31 merged; extraction obstruction, lead direction on owned-reference style

Merged `codex/cx-prover-commit31-20261022` (report
`r1p-final/PROVER-COMMIT31-20261022.md`). Added cfg(kani/aeneas_ref)-only
`sim_owned31.rs` (owned publication reference); five focused Kani checks pass;
all three frozen ELFs rebuilt byte-identical, 493-file inventory matches.
Obstruction: Charon accepts the indexed owner (`has_errors=false`) but Aeneas
exits 2 at `sim_owned31.rs:151–159` (InterpMatchCtxs.ml:2739, loop fixed
point). No new Lean theorem; `RustProverRefinement` stays explicit.

Lead direction (AGENTS.md discipline §7, a repeated shared obstruction): parts
28–31 each stopped on an Aeneas/Charon loop or iterator limitation. What worked
(part 29 `fields20::validate`, part 30's callee split) was small, **structurally
recursive** functions over owned values, with no while loops, iterators,
BTreeMap, RefCell or `Instant` in the extracted code. Part 31's owner still
has while loops mutating a BTreeMap inside a function that also takes timings.
From part 32 on, an owned reference to be extracted must be: one function per
loop; structural recursion on an owned Vec or a counter; maps modelled as a
sorted association list, checked by Kani against the shipped BTreeMap
per transition (insert/entry-or-insert/iteration order); timing calls
removed (timings are not observable, D143). Verify each small function
separately before composing.

## D145 (lead, 2026-10-22 03:45): part 32 merged; correction to D144 on BTreeMap

Merged `codex/cx-prover-commit32-20261022` (report
`r1p-final/PROVER-COMMIT32-20261022.md`; relaunched once after a Codex
capacity error, with a WIP snapshot commit kept). Proved in Lean, for the recursive sorted-list
publication reference: lookup totality, insertion/replacement, query-order
publication, sortedness, uniqueness and byte comparison. Standard axioms; all
three frozen ELFs rebuilt byte-identical (cfg-gated `sim_owned32.rs`).
Obstruction: the Kani check of the shipped BTreeMap transitions times out
(600 s), even isolated.

**Correction (lead error in D144).** D144 asked for Kani checks "against the
shipped BTreeMap". That contradicts D133: BTreeMap internals are not verified;
`std::collections::BTreeMap` is a named trusted item (`ProverCommitTrustedStd24.TrustedStd`:
`btree_empty`, `btree_insert_state`, `btree_insert_previous`, `btree_get`,
`btree_iter_ordered`, specifying it by the universal `Std.TreeMap` model). The
timeout is the predictable cost of that mistake. Corrected route: verify the
shipped *loop logic* with Kani with BTreeMap stubbed by an implementation of
exactly the TrustedStd contract (the sorted-list model), and connect the
native loop to the reference in Lean via the TrustedStd fields. If the shipped
code uses `entry(..).or_insert_with`, add it to TrustedStd as one more named
field with its documented semantics (get, then insert if absent), recorded
visibly on the trust list. Do not add any other field.

## D146 (lead, 2026-10-22 04:10): part 33 merged; correction to D143 ruling 1; statement-domain ruling

Merged `codex/cx-prover-commit33-20261022` (report
`r1p-final/PROVER-COMMIT33-20261022.md`). Per D145: exactly one TrustedStd
field added, `btree_entry_or_insert_with` (hit: map unchanged, callback not
invoked; miss: callback invoked once, value inserted and returned), a named Prop
hypothesis, not an axiom. Proved: folded-loop, ordered-consumer, query-answer,
merge and sorted-lookup transport; one bounded Kani lazy-entry transition
check. Standard axioms; no shipped change.

**Correction (lead error in D143 ruling 1).** D143 said model statement fields
"are typed in K, hence canonical", so the Rust rejection branch would be
unreachable. That is false: `ProverCommitPublicImage33` proves that `K` is
`WideExact`, not M31 (an asset id can be the tower element `i`), and
`nextPairIndex : Nat` can be 2^64, beyond u64. So no field-preserving source
image exists for every model statement. The worker correctly stopped rather
than add an unannounced admission premise.

**Ruling (announced statement domain).** The deployed privacy claim ranges
over the statements the deployed system can express: model statements that
are the image of a shipped `r0::Public` value whose `public_bytes` returns
`Ok`. Statements outside that image have no deployed counterpart. For them, the
deployed prover returns an error before producing any proof, and nothing is
published. That must be stated and proved as part of the domain. This is a
restriction of the statement domain to what is representable, and it does
not restrict the adversary. Within the domain the statement may still be
adversarially chosen, and the queries remain arbitrary. The endpoint must show
the before/after quantifier on `x`, and the report must mark this as a scope
statement, visible in the headline, not a hidden premise.

## D147 (lead, 2026-10-22 04:50): part 34 merged; ruling on OS entropy and ledger failures

Merged `codex/cx-prover-commit34-20261022` (report
`r1p-final/PROVER-COMMIT34-20261022.md`). Proved: the D146 statement domain
(`ProverCommitDomain34.DeployedStatement`) with exact `public_bytes`
agreement; no publication outside it; the structural eight-attempt retry
owner (two native Kani control checks), keeping entropy errors distinct from
retryable rejections; separate OS-failure and zero-exhaustion events, with
zero exhaustion ≤ 3/2^256 on a uniform raw carrier. J9095 standard axioms;
no shipped change, TrustedStd unchanged.
Stop: source control gives no OS-error bound below 1 (proved), so OS and
filesystem failures cannot be charged as a small δ.

**Lead ruling: OS and filesystem are an adversarial environment, not a
probability term.** Do not add a δ for OS/fs failure and do not assume an
error-free OS. Instead:
1. Model `getrandom::fill` outcomes, reservation create/write/fsync results
   and duplicate-nonce errors as an **environment schedule chosen by the
   adversary**, as a function of the call sequence (call index, call kind,
   prior outcomes). The schedule must not see the secret bytes being
   written: the OS is not assumed to leak file or RNG contents to the
   adversary.
2. Prove fail-closed behaviour on every failure path (`state_only_entropy.rs`
   172–196 and 919–962, `prover.rs` 354–375): nothing witness-dependent is
   published. Only a witness-independent error outcome is observable, and
   the simulator can reproduce it from the same schedule.
3. One named environment trust item, **E1 (OS RNG):** when `getrandom::fill`
   returns Ok, its bytes are uniform and independent of everything else.
   Record it on the trust list next to TrustedStd and P7, visible in the headline.
   The existing zero-exhaustion term 3/2^256 stays in the bound.
This makes privacy hold for every failure schedule, which is stronger than
any probability bound on failures.

## D148 (lead, 2026-10-22 05:20): part 35 merged; D147 refined: private ledger plus byte-blind faults

Merged `codex/cx-prover-commit35-20261022` (report
`r1p-final/PROVER-COMMIT35-20261022.md`). Proved: the byte-blind environment
schedule, `fail_closed` and `failure_replay` (on any failure the real and
witness-free simulator prefixes have identical observables, pointwise for
every schedule, with no OS/fs probability charge), reservation retention, the
extracted reservation bridge, and the E1-conditional zero-candidate bound.
Native control checks pass; J9127, 16 theorems, standard axioms; no shipped
change.
Finding: D147's schedule (seeing only index, kind and prior statuses) cannot
reproduce native `create_new`, whose occupied/fresh outcome depends on
whether the reservation path is already in the ledger (Lean proof plus a
real-filesystem probe). That is a lead modelling error in D147, not a privacy
problem.

**Refinement of D147.** The filesystem has real state. Model the reservation
ledger as **private environment state** with faithful `create_new`
semantics: it preserves existing entries and returns AlreadyExists iff the
path is present. The byte-blind adversarial schedule injects faults
(getrandom, create/write/fsync failures) around it. The adversary may choose
the initial ledger and add entries, byte-blind: chosen without seeing
any secret seed or path. A fresh path colliding with an adversary-chosen
entry is a bad event, bounded from E1 by (number of entries × attempts)/|path
space|, stated numerically. Add one named environment item, **E2
(filesystem):** `create_new` is atomic create-if-absent (O_EXCL), and
written/fsynced data persists. It sits on the trust list beside E1, TrustedStd
and P7. The reservation path is not made public.

## D149 (lead, 2026-10-22 05:30): part 36 merged; reservation address law comes from P1

Merged `codex/cx-prover-commit36-20261022` (report
`r1p-final/PROVER-COMMIT36-20261022.md`). Proved on the D148 model: private
ledger membership with byte-blind faults, retention, duplicate handling,
`fail_closed`/`failure_replay`; the exact E1 push-forward; the entry-count
union bound with the address-law hypothesis visible; a consistent E2 model.
J9134, 15 theorems, standard axioms; no shipped change.
Finding: E1 and E2 do not by themselves imply that SHA-256-derived
reservation paths avoid adversary-chosen entries (`E1_E2_without_uniform_paths`;
for a generic hash, a constant address function gives mass 1). Correct: that
inference needs a property of the hash.

**Ruling.** The address law comes from **P1**, the random-oracle model for
SHA-256 that the whole privacy and soundness argument already uses. No new
assumption is added. Obligation: under P1, for adversary-chosen entries
and every prior context, a fresh reservation address lands on an entry with
probability ≤ (entries + queries that hit the same input)/2^256. The part
"the adversary queried the oracle on this nonce input" is covered by the
existing seed-guess event. **Check domain separation:** the reservation hash
input must be disjoint from the protocol's oracle inputs (tag or length
prefix). If it is, it is an independent ROM coordinate. If it isn't, prove
the overlap is harmless or report it as a source finding. Do not change shipped
code.

## D150 (lead, 2026-10-22 05:45): part 37 merged; a new explicit reservation-guess event

Merged `codex/cx-prover-commit37-20261022` (report
`r1p-final/PROVER-COMMIT37-20261022.md`). Proved under P1 the fresh-address
entry bound and the frame separation of the reservation input from the
simulator-seed frame; control proofs for all 0–15 rejected nonce prefixes.
J9151, 19 theorems, standard axioms; no shipped change.
Finding (`no_existing_event_containment`): an adversary oracle query on the
reservation input (a memo hit) is **not** contained in the existing
`ProverCommitSeedEvent19.seedGuess`, which tests only the prefix
`UNPROVED:R1:SIM:COIN || simulatorSeed`. So D149's statement that the seed-guess
event already covered this was wrong (lead error).

**Ruling.** Add one new, explicit bad event, `reservationGuess`: some
adversary oracle query (or adversary-chosen ledger entry) equals a
reservation input or path the prover generates. Bound it by the same counting as
`seedGuess`: with a byte-blind adversary and uniform nonzero 32-byte nonces
(E1), the mass is ≤ (Q + entries) · attempts / (2^256 − 1) per run. Add that
term, stated numerically, **visibly to the headline bound** (before/after
shown) rather than absorbing it. At protocol parameters it is far below the
existing terms, so the < 2^-100 conclusion should still hold; prove that
inequality, do not assert it.

## D151 (lead, 2026-10-22 05:55): part 38 merged; ledger collisions coupled exactly, memo hits under the existing query budget

Merged `codex/cx-prover-commit38-20261022` (report
`r1p-final/PROVER-COMMIT38-20261022.md`). Proved: `reservationGuess` and its
fixed-context counting bound; and, conditionally on Q, entries ≤ 2^64, the
< 2^-100 numeric conclusion. The cap was not installed in the endpoint. J9159,
15 theorems, standard axioms; shipped files byte-identical.
Finding: under D148 the adversary may plant any finite ledger, including
every path, so charging the whole `reservationGuess` mass gives 1. Correct;
D150's charging of ledger entries was the wrong shape (lead error).

**Ruling (two parts).**
1. **Ledger collisions are coupled exactly and charged nothing.** The nonce and
   its reservation path are witness-independent coins. The real and simulated
   runs use the same nonce coins and the same ledger. A collision gives
   AlreadyExists, then the fail-closed/duplicate path, identically in both
   worlds. Obligation: prove the nonce and path are drawn and used before, and
   independently of, any witness-dependent value (if not, report it as a source
   finding). Then the ledger needs no size cap and contributes no term.
2. **Memo hits are charged under the existing query budget.** An adversary
   oracle query equal to a generated reservation input reveals the nonce-derived
   value. Charge ≤ Q · attempts / (2^256 − 1) with the same Q ≤ 2^64 query budget
   the headline already uses for `seedGuess` (`ProverCommitSeedEvent19.budget
   (2^64)`). That is not a new restriction, and it is shown visibly in the bound.

## D152 (lead, 2026-10-22 06:10): part 39 merged; the mask nonce is public and adversary-chosen

Merged `codex/cx-prover-commit39-20261022` (report
`r1p-final/PROVER-COMMIT39-20261022.md`). Proved
(`ProverCommitLedgerCoupling39`): exact shared-ledger coupling for every
finite ledger and schedule (state equality of the reservation transition and
preparation prefix; collision implies duplicate, which stops both worlds
identically). No ledger cap, no collision term. Also the conditional memo
counting and < 2^-100 arithmetic. J9171, 18 theorems, standard axioms;
shipped files byte-identical.
Source finding (correct, and a lead error in D151): the deployed proof-account
route calls `generate_for_mask_nonce(mask_nonce)` (`state_only_entropy.rs`
202–224). The nonce is the caller-supplied proof-account public key (D38.4),
not an OS draw. Only the 64 bytes of field entropy and leaf seed come from the
OS. So D151's "the nonce is a uniform witness-independent coin" is false for
the deployed path.

**Ruling.** Model the mask nonce as **public and adversary-chosen**: quantify
over it, and let the adversary pick it, possibly after earlier queries.
Classify every hash input on this path by whether it contains private
OS-drawn bytes:
- Inputs built only from public data (the nonce, public statement) are public
  oracle queries. The adversary may query them in advance, and the coupling
  preserves them exactly in both worlds, with no charge (as the worker
  recommends). The reservation path, if it depends only on the nonce, falls
  here, and duplicates take the coupled fail-closed path (that is the
  ledger's job: no mask reuse for a nonce).
- Inputs containing the private 64 seed bytes are charged a memo-hit term,
  ≤ Q · attempts / 2^256 per 32-byte seed under the existing Q ≤ 2^64 budget,
  visibly in the headline.
Do not switch the target to the 96-byte `generate()` adapter. The deployed
route is the proof-account route.

## D153 (lead, 2026-10-22 06:30): part 40 merged; public binding inputs need a conditional ROM law

Merged `codex/cx-prover-commit40-20261022` (report
`r1p-final/PROVER-COMMIT40-20261022.md`). Proved: private-seed memo counting
with visible additions 4·Q·attempts/2^256 + 48/2^256, keeping < 2^-100
(conditional on the remaining joins); the public-nonce preparation model with
the part-39 ledger coupling kept; an exhaustive hash-family classification on
the deployed path (`ProverCommitHashClass40.classify`, `hash-input-inventory.json`).
J9186, 30 theorems, standard axioms; shipped files unchanged.
Lead check of the classification: the masks, D-seed, leaf salts and Merkle
nodes all derive from the private OS bytes (field entropy, leaf seed). The
public-only inputs (public bytes, reservation, precommit and attempt
bindings) carry no secret. So the public nonce is **not** a privacy attack.
Obstruction: the old commitment argument (`EventsR1PBin.hit_cm`, `HitFresh`)
assumed the first binding input was fresh, which is false once the nonce is
public: the adversary can pre-query it with probability 1.
Next (part 41): replace that use of `hit_cm` with the worker's specified
public-prefix-aware conditional ROM law. Start from the adversary's prior
queries and answers, reuse both binding answers in the same ROM, reserve the
nonce in the shared ledger, and expose fresh private-derivation coordinates
only outside the two raw-seed memo events. Then transport the joint adaptive
law (with duplicate termination and retained rejected-attempt history) to the
successful continuation, keeping the existing bounds on private-derived reads.
No new trust item, nonce law or ledger cap.

## D154 (lead, 2026-10-22 06:45): part 41 merged; conditional ROM law proved locally

Merged `codex/cx-prover-commit41-20261022` (report
`r1p-final/PROVER-COMMIT41-20261022.md`). Proved: the conditional
public-prefix ROM law with retained adaptive histories; preservation of the
public binding answers; memo-aware mixed-read agreement; the verifier's
opening log is unchanged when the binding answers are replaced. The selected
64-byte native entropy API passed its bounded control check, and its structural
reference translates through Charon/Aeneas. 20 theorems, standard axioms;
shipped files byte-identical. The job stopped because its env J allocation
(9187–9399) was exhausted, not on a proof obstruction.
Next (part 42, env J 9400–9799): instantiate the concrete `gAddr`/`attVec`
conditional private-read bounds and the successful-continuation transport;
the Lean bridge for the 64-byte owner and reservation-history composition;
then publication, FS conversion, the joins and the endpoint.

## D155 (lead, 2026-10-22 07:35): part 42 merged; private-read bounds instantiated

Merged `codex/cx-prover-commit42-20261022` (report
`r1p-final/PROVER-COMMIT42-20261022.md`). Proved: the private raw domains avoid
the public bindings; concrete public-normalised private-read bounds and charged
adaptive-hit bounds; global read agreement; the bridges from the generated
64-byte entropy owner to the model, the reservation state and the retry
callback. J9493, 56 theorems, standard axioms; shipped files unchanged; no new
trust item.
Obstruction (tool limit, no counterexample): the native Kani check of the
sixteen-candidate nonzero comparison loop over arbitrary bytes times out at
600 s; the isolated zero-test helper passes. Next (part 43): the P6 route:
per-candidate native transition check, then a Lean induction over the 16
iterations (as for the walk rows in part 30); then publication, FS conversion,
joins and endpoint.

## D156 (lead, 2026-10-22 08:15): part 43 merged; BTreeSet::from_iter joins TrustedStd

Merged `codex/cx-prover-commit43-20261022` (report
`r1p-final/PROVER-COMMIT43-20261022.md`). Proved: the native entropy candidate
transition (per-candidate Kani with the zero-test contract) composed through
the sixteen iterations in Lean, which closes D155; publication caller lemmas
with ordered byte control; exact native node padding. J9535, 33 theorems,
standard axioms; no shipped or trust change.
Obstruction: the parent-node collection uses `BTreeSet::from_iter`, which
extraction leaves as an external template.

**Ruling (same policy as D133/D145).** `std::collections::BTreeSet` is a
standard collection; do not verify its internals. Add exactly one named
TrustedStd field for `BTreeSet::from_iter` followed by iteration: the
result iterates the input's distinct elements in ascending order, i.e. the
sorted, deduplicated list (`List.mergeSort` of `List.dedup`, or the
`Finset` sort). Record it visibly on the trust list. Then prove that the
parent traversal built on it is sorted and duplicate-free, and that it
preserves the subsequent coin order.

## D157 (lead, 2026-10-22 08:35): part 44 merged; standing rule for std collection methods

Merged `codex/cx-prover-commit44-20261022` (report
`r1p-final/PROVER-COMMIT44-20261022.md`). Added the D156 TrustedStd field for
`BTreeSet::from_iter`. Proved: sorted, duplicate-free parent traversal with
coin order and state preserved; the native parent transition (536 Kani checks)
composed through all 18 tree levels. 15 theorems, standard axioms; shipped
files unchanged.
Obstruction: `BTreeMap::len` (which controls the final `program_tree`
Merkle-error guard) is not among the TrustedStd fields and cannot be derived
from them (countermodel). The direct native `indices.sort(); indices.dedup()`
Kani diagnostic timed out at 600 s and was not rerun.

**Standing rule (to stop one ruling per std method).** Extending D133/D145/D156:
a worker may add a named TrustedStd field, without waiting for a lead ruling,
for any **pure** std collection or slice method the shipped code actually
calls (constructors, observers, `len`, `sort`, `sort_unstable`, `dedup`,
`from_iter`, `iter`/`into_iter`, `contains`, `get`, `insert`, `remove`). The
field must state exactly the method's documented semantics against the Lean model
(`Std.TreeMap`/`TreeSet`, `List`), and the report must list every field added,
with the call site. Not covered by this rule: anything with I/O, allocation
failure, concurrency, interior mutability, hashing (`HashMap` ordering) or
unsafe code. Those still need a ruling. So `BTreeMap::len` (= model size) and
`slice::sort` + `Vec::dedup` (= sorted dedup list) are covered.

## D158 (lead, 2026-10-22 08:50): part 45 merged; ProgramOne digest as state passing

Merged `codex/cx-prover-commit45-20261022` (report
`r1p-final/PROVER-COMMIT45-20261022.md`). Added three D157 TrustedStd fields
(map length, scalar sort, dedup; listed with call sites). Proved: sort/dedup
and length transport; the eighteen-level Merkle-error guard; transcript
merge and read-count transport. J9636, 14 theorems, standard axioms; shipped
sources unchanged.
Obstruction: `ProgramOne::digest` mutates a shared `RefCell` programming table
and collision flag, and its extracted return exposes neither. A countermodel shows
that equal digest returns can lead to different publication outcomes. The worker
correctly did not add an interior-mutability trust law.

**Ruling (same route as D136/D137 for CoinOracle).** This is not a new trust
law. Interpret `ProgramOne::digest` as **state passing**: each call takes and
returns `(table, collision flag)` explicitly. Prove per call, with a Kani check
of the shipped RefCell code against the state-passing reference, that it
returns exactly the updated table and flag. Then reuse the part-28 generic
monadic state lift to thread the state through the publication continuation.
The single-thread fact needed for RefCell is the TLS single-thread item
already on the trust list. Nothing is added.

## D159 (user decision, 2026-10-22 10:20): side channels are in the privacy contract

The user ruled ("cover them") that timing and other side channels are **inside**
the privacy contract. This reverses the scope line in D143 rulings 2 and 3, which had put
them out of scope. It raises the target and does not lower it. Attempt counts,
retry counts and timings are now treated as potentially observable.

Leakage model, in three levels, each stated separately and never merged:
- **L1 (outcome counts):** the adversary sees the number of attempts/retries,
  which call failed, error codes, reservation/ledger effects and the number,
  order and sizes of everything the prover sends or writes. Proof obligation: the joint
  law of these is simulatable without the witness (witness-independent, or a
  function of public data and the simulator's own coins).
- **L2 (source-level trace):** the sequence of branches taken, memory/array
  indices, collection operations with key-dependent cost (e.g. BTreeMap
  insertion paths), allocation sizes, loop trip counts and variable-latency
  operations (division, inversion, early exits) must be witness-independent.
  Formal route: relational (2-run) properties over the extracted/owned code
  and Kani self-composition per function.
- **L3 (compiled code and hardware):** compiler and CPU constant-time
  behaviour **cannot be fully proved here**. It is either a named trust item
  (the compiler preserves L2 constant-time; the CPU's used instructions have
  data-independent latency), or measured (dudect-style tests, labelled as
  measurement, never as proof).
A witness-dependent retry or rejection-sampling count (for example a P_R1
predicate whose acceptance depends on the witness) would be a protocol-level
leak, and its fix (constant-work attempts or a witness-independent
acceptance law) would be a change to the frozen prover. Any such
finding is escalated to the user with a recommendation and is not patched silently.
First step: a side-channel inventory of the deployed prover path
(`r1p-final/SIDE-CHANNEL-AUDIT-20261022.md`), running alongside privacy
part 46.

## D160 (lead, 2026-10-22 10:40): part 46 merged; publication composed, source-view byte image next

Merged `codex/cx-prover-commit46-20261022` (report
`r1p-final/PROVER-COMMIT46-20261022.md`). Per D158: `ProgramOne::digest` is
certified as state passing (per-call Kani against the reference) and threaded
with the part-28 lift; binary multiproof transitions and child-map support are
verified; compact proof-byte publication and exact table/flag finalisation are
composed. J9691, standard axioms; shipped files unchanged.
Obstruction: the byte-image bridge from `sim::semantic`/`sim::opening` outputs
to the model payload, starting with `y1`. A counterexample shows that codec
success alone does not give the image. It is not a privacy attack.
Next (part 47): that bridge, field by field. Per D159, the source-to-
`FSExperiments` conversion now has to carry the L1 observables too, so part 47
stops before the conversion and waits for the side-channel audit.

## D161 (lead, 2026-10-22 10:55): side-channel audit merged; three user decisions raised

Merged `codex/cx-sidechannel-20261022` (report
`r1p-final/SIDE-CHANNEL-AUDIT-20261022.md`, evidence `sidechannel-20261022/`):
a source inventory of the proof-account prover route (55 pinned files), eight
findings, and nine Python source-expression checks. These are not Kani or Lean
proofs and not measurements. No shipped change.
Findings, lead summary:
- **F1 (L1):** the retry decision includes the no-pole check, which reads the
  unmasked witness tuples. The attempt count is therefore not exactly
  witness-independent. Its effect is bounded by the pole probability, about
  |S|/|K| ≤ 4096/2^124 per attempt, which the privacy bound already charges.
  So L1 can be met statistically by proof work (the coupling extended to the
  whole attempt record), with no code change. Exact independence would
  need a prover change.
- **F2 (L2):** canonical field arithmetic branches on operand values
  (`if x >= P` in add/sub/reduce; zero tests). On masked witness cells, the
  branch probability depends on the witness. That is a real L2 timing/branch leak,
  not closable by proof. It needs constant-time field kernels on the prover side.
- F3 (private-coin rejection counts): witness-independent; proof work.
  F4 (canonicality and balance guards): constant on the honest domain; proof
  work. F5/F6 (challenge-derived indices, sparse evaluation, query scan,
  Merkle sharing, checker elimination, simulator BTree costs): depend on
  Fiat–Shamir values, so either a simulatability proof or oblivious
  rewrites. F7: production TLS instrumentation retains per-check
  timings and rejected-attempt challenge values, and `attempts` is
  returned. These are host-observable.
- **F8 (deployment):** no checked-in caller uses the audited proof-account
  route. The R1 devnet runner calls `prove_masked_retrying`, which uses the
  96-byte `generate()` (OS-drawn nonce); the live wallet adapter uses
  `generate_for_mask_nonce` with the older V7 prover. The deployed prover route
  is therefore not pinned.
- L3: the prover is native host Rust (std, OS RNG, filesystem, TLS). The only
  recorded target is x86_64-unknown-linux-gnu with rustc 1.94.1; no CPU or
  binary pin.
Raised to the user (escalation per AGENTS.md §8): the deployed route (F8),
whether to change the host prover for L2 (F2, F5–F7), and the L3 platform.
Proof-only L1 work proceeds meanwhile.

## D162 (user decisions, 2026-10-22 11:05): route, constant-time prover, L3 platform

The user decided the three D161 questions, each as the lead recommended:
1. **Deployment route = proof-account route** (public nonce = proof-account key,
   `generate_for_mask_nonce` → `prove_masked_retrying_with`), per the documented
   design (D38.4). The client/caller will be changed to call it, with new source
   pins and integration receipts. That is a host/client change; no verifier
   change. The devnet runner's 96-byte route is not the target.
2. **Constant-time host prover (L2).** Add constant-time field kernels and
   fixed-shape loops on the prover side only, and gate off TLS instrumentation
   in production builds. Constraints: the verifier ELFs stay byte-identical
   (dfc2a91a…, fb2fc048…, 121f3e29…); proof bytes are unchanged; each kernel
   gets a Kani/Lean equivalence proof to the current arithmetic and a two-run
   branch/index-trace check. It is an adoption candidate on its own branch,
   note-before-code, and is not frozen until its gates pass. Prior prover source
   pins are re-checked against it.
3. **L3 platform = x86_64 Linux native.** Pin the binary, compiler and flags, and
   a CPU model. L3 evidence is a disassembly audit plus dudect-style
   measurements, labelled as measurement, with compiler/CPU constant-time named
   as trust items.

## D163 (lead, 2026-10-22 11:50): L1 model layer merged; CT-kernel candidate passes against the new ELF pins

Merged `codex/cx-l1-coupling-20261022` (report
`r1p-final/SIDE-CHANNEL-L1-20261022.md`), proof-only. Proved: an ordered L1
attempt record with retry-control erasure; the conditional retry hazards and
iteration-entry laws for all eight attempts; capped two-seed entropy symmetry
and the ideal draw-count law; generic joint-TV union tools, with a numerical
candidate below 2^-100 that is **not** yet an established native bound.
J9880 standard axioms; no shipped change. No TLS leak or valid-spend
counterexample was found. Open: native event-producer refinement; the
joint mask/count/TLS/oracle coupling; equal-circle and query-abort integration;
composition with part 47.
Constant-time kernel candidate (`codex/cx-ct-kernels-20261022`, kept unmerged
as a candidate per D162; report `design/CT-KERNELS-20261022.md`): the design
note came first; branch-free M31/CM31/QM31/WideExact kernels behind a host-only
feature; TLS instrumentation gated off in production; 69 Kani harnesses
(equivalence plus two-run trace) and 41 native tests pass; transfer and withdrawal fixture
proofs are byte-identical. Its builds give default `40dc7574…`, devnet
`12cb0bc2…`, Pool `121f3e29…`. Those are exactly the current pins after the
user-approved S4 adoption (C3-BIN addendum 11:50), so the ELF gate **passes**:
verifier bytes are unchanged by the candidate. Single-run fixture measurements:
transfer 41.74 → 39.01 s, withdrawal 38.94 → 42.23 s (measurement only).
Remaining L2 items: sampler, sparse evaluation, query scan, multiproof
sharing, checker.

## D164 (lead, 2026-10-22 12:25): part 47 merged; y1 image proved for the owned reference

Merged `codex/cx-prover-commit47-20261022` (report
`r1p-final/PROVER-COMMIT47-20261022.md`). Proved: release field normalisation
and canonical embedded arithmetic; the recursive basis/evaluator with subfield
range and exact decoding; the owned reference's exact byte image for all 29 `y1`
lanes. J9799 standard axioms; shipped files unchanged; no new trust field.
Open: binding the **shipped** `sim::semantic`/`sim::opening` to the owned
reference. The worker retried Aeneas on shipped loops and iterators, which fails.
Lead direction: the shipped side never goes through Aeneas. Use the P6 route
that worked in parts 29–30 and 43–44: a per-iteration Kani check
(shipped iteration = owned iteration, verified stubs for callees), then a Lean
induction over the owned loop. The constant-time candidate (D162) does not touch the
simulator, so this binding remains valid if the candidate is adopted.

## D165 (lead, 2026-10-22 12:50): constant-time stage 3; cost and a design question

Candidate branch `codex/cx-ct-kernels-20261022` (head `47397e5e16`, unmerged
per D162; reports `design/CT-KERNELS-20261022.md` and
`CT-CHECKER-ASSESSMENT-20261022.md`). The ELF gate is corrected to PASS against the
adopted pins. Stages 3(a)–(e) are done with equivalence gates (Kani, exhaustive or
per-step), paired source-trace checks, ELF identity and byte identity of the
fixture proofs and public bytes: fixed-shape samplers; constant-work bounded
rejection with the legacy stream state; a fixed tensor schedule for equality
weights; a full-pair QueryScan with masked selection; oblivious multiproof
sorting and sharing with fixed slots. Single-run prover wall time
(transfer/withdrawal, measurement only): baseline about 40 s; after (a) 44/43;
(b) 53/52; (c) 161/137; (d) 192/202; (e) 176/166.
Stopped at (f): a generic padded constant-shape P_R1 elimination costs
80.1 billion M31 coefficient updates per attempt (source bounds; not a
lower bound for every algorithm). A structure-specific emitter would be needed.
Lead assessment: items (c)–(f) are **challenge-dependent (c-q)** and (a)–(b) are
**private-coin-dependent (c-s)**. None reads the witness directly. Their source traces are
functions of public data, Fiat–Shamir challenges and independent coins, so
L2 can instead be met by proving that this trace is **simulatable**: its joint law
equals the simulator's up to the existing bad events. That gives an identical
timing distribution in the real and ideal worlds, and needs no constant-time rewrite.
The field arithmetic on witness-bearing values (F2) and the pole check (F1) read
secrets directly and keep the constant-time kernels. Raised to the user.

## D166 (user decision and lead, 2026-10-22 18:20): L2 by simulatable trace; part 48 merged

**User decision (answering D165):** L2 for challenge- and private-coin-dependent
steps is met by proving the source trace **simulatable**: its joint law in the
real run equals the simulator's, up to the existing bad events. It is not met
by constant-time rewrites. Constant-time kernels stay only where secrets are
operands: the field arithmetic on witness-bearing values (F2) and the pole-check
arithmetic (F1). Consequence for the candidate: keep stage 2 (field kernels and
TLS gating), and drop the stage 3(a)–(e) fixed-shape rewrites from the
adoption candidate (they stay on the branch history as measured evidence). This
should restore prover time near the ~40 s baseline. The simulatable-trace
obligations for F3, F5 and F6 join the L1 coupling as proof work.
Part 48 merged (`codex/cx-prover-commit48-20261022`, report
`r1p-final/PROVER-COMMIT48-20261022.md`): native iteration bindings by
per-iteration Kani with owned-loop induction (the D164 route); interpolation
equal to `Lagrange.interpolate` with its 896-byte image; primal and dual folds;
gamma/kappa powers; seven-coefficient round accumulation. J9999 standard
axioms; shipped files unchanged. Stopped on an exhausted env J range. Open:
semantic samples and guards, final shift, weight-model correspondence, caller
composition.

## D167 (lead, 2026-10-22 18:50): constant-time candidate v2 per D166

Branch `codex/cx-ct-kernels-v2-20261022` (head `2b7a80b65a`, an unmerged adoption
candidate; v2 section in `design/CT-KERNELS-20261022.md`). It holds only the stage-2
field kernels and TLS gating plus a constant-trace pole check (`ct_pole.rs`):
branch-free QM31 equality and an eager scan over every slot, with no early exit.
Six compositional Kani gates, instrumented two-run checks and a full-size native
trace replay pass, and so do the fixture pole regressions. The verifier ELFs match
the adopted pins, and the fixture proof/public bytes are identical. Single-run
prover wall time (measurement only): transfer 38.51 s, withdrawal 37.95 s,
back at the ~40 s baseline. The stage-3 rewrites stay only on the old branch.
Remaining for L2: the simulatable-trace proof for the F3/F5/F6 steps (listed by
file:line in the v2 section); then candidate adoption gates and the L3 receipt.

## D168 (user feedback, 2026-10-22 18:55): prover slowdowns need a stop gate

The user called the stage-3 constant-time slowdown (about 40 s to 170–200 s)
unacceptable. It was never adopted: the v2 candidate (D167) is at the ~40 s
baseline. The process failure was the lead's. The stage-3 prompt had no
performance stop condition, so five successive slowdowns ran to completion
before review. From now on, every job that changes prover or host code carries a wall-time
budget gate: measure after each step and stop and escalate if any fixture's prover time
rises more than 10% over baseline. The stage-3 branch is evidence only and is
not a candidate.

## D169 (user, 2026-10-22 19:00): stage-3 branch removed; prover target under 15 s

On the user's instruction ("remove that shit if needed"), the stage-3
fixed-shape branch `codex/cx-ct-kernels-20261022` was deleted. It was never in
research. Its measurements are kept in D165; the v2 candidate is unaffected.
**New user target: prover wall time under 15 s per proof** (about 38–42 s today,
single-run on the x86_64 Linux build host). This is a performance requirement
alongside the security contract, not a replacement for it. Next: a profiling
job, with per-phase time, retry count and thread use, and a ranked list of
speedups classified by whether proof bytes and the existing proofs/trust
items survive. Notes: parallelism would touch the single-thread TLS trust item
and the side-channel model; any change to proof bytes touches the verifier
and soundness model and needs the user's approval.

## D170 (lead, 2026-10-22 19:20): prover profile; P_R1 is 89% of prover time

Merged `codex/cx-prover-speed-20261022` (measurement only;
`design/PROVER-SPEED-20261022.md`). Five runs per fixture and variant on the build
host (Intel Core Ultra 7 155H, 16 cores/22 threads, rustc 1.94.1), medians:
research 37.25/37.24 s and CT v2 37.58/37.44 s (transfer/withdrawal); one
attempt in every run. **P_R1 takes about 33 s**: emit 12.3, convert 4.7, build
7.1, check 8.8. Everything else is about 4.3 s: semantic sumcheck 2.5,
commitments and encodings 1.2, salts, hashing and Merkle under 0.7. So
hashing and Merkle parallelism cannot reach the 15 s target. The target needs about a
4x speedup of P_R1 (projected 12–13 s end to end). These are projections, not results.
Next, per D169: a byte-preserving P_R1 speedup on the v2 candidate branch, using
bounded workers, exact blocked/SIMD M31 arithmetic and removal of duplicated
column construction. Accept/reject decisions and proof bytes stay identical,
there are new Kani equivalence gates, and the deterministic exact checker stays
(no randomized checking). P_R1 inputs are public challenges, so its trace falls under the D166
simulatable-trace route. Workers change the thread model, so the TLS
single-thread trust item must be re-examined (v2 already gates TLS recording off).

## D171 (lead, 2026-10-22 20:45): P_R1 speedup on the v2 candidate, 37 s to 17.5 s

On `codex/cx-ct-kernels-v2-20261022` (unmerged candidate; `design/PR1-SPEED-20261022.md`):
step 1 (descriptor sharing) gave no gain and was reverted, with the negative result
kept. Step 2 adds exact blocked arithmetic with two-fold Mersenne reduction (five Kani
obligations). Step 3 adds bounded deterministic workers (at most 16 threads, fixed merge
order) across emitter families, target rows, converter images, checker rows and
builder columns. Median of 3 runs: P_R1 12.24/12.49 s, end-to-end **17.49/17.58 s**
(transfer/withdrawal), from about 37–39 s. Every step: 1,000-challenge differential
with zero verdict mismatches, byte-identical proof and public bytes, strict
and dense verification, all three ELF pins rebuilt identical. An earlier stage-3
form measured 16.0 s but did needless work on rejecting challenges. The final form
fixes that at about +1.5 s on the accepting path; this trade-off is to be revisited.
Under 15 s is not met yet. Remaining large items: emitter insertion (largest
P_R1 phase), and the non-P_R1 remainder of about 5 s (semantic sumcheck point claims
about 2.1 s over 28k independent evaluations; 29 lane encodings about 1 s), both
parallelisable over public shapes. Trust note: the prover is now explicitly
multithreaded in P_R1, on public data only. The TLS single-thread item is restated
to cover only the gated-off recorder; the quiet panic hook covers the workers.

## D172 (lead, 2026-10-22 21:05): prover under 15 s on the build host (v2 candidate)

Step 4 on `codex/cx-ct-kernels-v2-20261022` (head `b2f95e269a`, unmerged candidate).
(a) Reusing the first-lift rank result across certificate workers recovered the
accepting path: 16.19/16.18 s. (b) Parallel emitter insertion gave no gain and was reverted.
(c) Semantic sumcheck evaluations and lane encodings now run on 16 workers with fixed
public work ranges and a deterministic merge; constant-time kernels are unchanged;
two-mask traces show partition and work counts are independent of secrets.
**Median end-to-end 13.63 s (transfer) and 13.98 s (withdrawal)**, from about 37–39 s.
The user's under-15 s target is met on the build host. Every step kept byte-identical
proof and public bytes, zero verdict mismatches over 1,000 challenge sets, local Kani
gates and the three ELF pins.
Caveats: measured on a 16-core/22-thread Core Ultra 7 155H; the time scales with
the client's cores and is not a guarantee for smaller machines. The candidate is not
adopted. Adoption still needs the native refinement rebinding for the changed P_R1 and
evaluation code, the D166 joint trace transport, the expanded thread/TLS model, and
the L3 receipt on the pinned platform.

## D173 (lead, 2026-10-22 21:30): part 49 merged; simulator payload equality still open; cost control

Merged `codex/cx-prover-commit49-20261022` (16 commits; report
`r1p-final/PROVER-COMMIT49-20261022.md`). It covers statement points and
point-weight callers, circle factors, the inactive table, native power/inverse
kernels, the final half-shift and Libra column, raw coefficients, the full
materialised weights with R1 functional correspondence, and the complete owned
opening kernel with ordered coefficient bytes. Its final audit imports 93 modules
and checks 241 theorems, standard axioms only. Shipped files unchanged.
It stopped on an exhausted env J range (10000–10199). Six interfaces remain
before native simulator output = `R0Z.RefPayload.simE` payload: the
`qm31_sum_products_small::<3>` composition; the optimised
`evaluate_state_only_polynomial` caller; the semantic oracle value
(maskLinear + sem14·terminalValue, with the sparse-equality pruning and the
P_R1 good-domain condition, including α9 ≠ ½, for the full caller); `Weights::new` outer
composition and gamma batching; the source `encode_at`/`eval_at`/`nodes_for`/
`phi_inverse`/leaf bindings; the final payload composition.
Cost: part 48 used about 0.9M tokens and part 49 about 1.3M, against a requested
0.4M. The worker cannot see its own token use, so from part 50 the env J range
is the budget: 100 compile numbers per part.

## D174 (lead, 2026-10-22 22:30): part 50 merged; budget held; two integration blockers

Merged `codex/cx-prover-commit50-20261022` (report
`r1p-final/PROVER-COMMIT50-20261022.md`). It used about 0.59M tokens, and the
J10200–10299 budget held. Proved: the owned three-product Karatsuba composition
(interface 1); the optimised degree-27 evaluator with prepared multiplication
(interface 2); sparse prefix products, ordered column sums, scanner provenance
and the owned sparse MLE model value; the selected-mask arithmetic kernels.
Standard axioms; shipped files unchanged. Blockers: (i) the integration audit
fails on duplicate, byte-identical `mul_m31` declarations in two extracted modules
(`Linear50`, `Batched48`). This is the known cross-extraction naming problem
(`IMPORT-UNION-20261021.md`), so apply the type-qualified naming fix or
alias one to the other. (ii) Caller composition hit the kernel memory limit. Per
AGENTS.md resource rule 5, it is not rerun with a larger cap: isolate the
declaration, inspect its reduction shape and split it with symbolic lemmas.
Next (part 51): both blockers, then interfaces 3–6.

## D175 (lead, 2026-10-22 23:15): part 51 merged; authorised cold build of the terminal cone

Merged `codex/cx-prover-commit51-20261022` (about 0.47M tokens; report
`r1p-final/PROVER-COMMIT51-20261022.md`). Fixed D174's blockers: the duplicate
`mul_m31` is replaced by reuse of the retained declaration; the memory-heavy caller
is split through symbolic result sequencing (no cap raised). Proved: the selected
mask coefficient producer and caller; all semantic mask column reads; the native
mask basis and semantic extra functional bound to model carriers; coefficient
provenance and the complete owned linear oracle value; terminal equality and the
arithmetic suffix. J10368, 73 standard-axiom audits.
Obstruction: the terminal integration imports a retained cone whose closure has
535 modules, 495 without Env J objects. Building them one compile number at a
time exceeds the budget. **Lead authorisation (AGENTS.md resource rules 1, 2 and 6):**
treat this as one cold dependency build on the build host, not as proof attempts. Run
one capped scope (MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0), reusing the pinned
cache, with aggregate RSS monitored and a stop if it nears the cap. Record target, exit, wall,
peak RSS and swap, under its own build label outside the proof-attempt range. A
module that fails or is memory-killed is isolated and reported, never rerun with a
larger cap. Session A's modules are only built, never edited.

## D176 (lead, 2026-10-22 23:40): part 52 merged; the import-union naming fix is now on the critical path

Merged `codex/cx-prover-commit52-20261022` (about 0.53M tokens; report
`r1p-final/PROVER-COMMIT52-20261022.md`). The D175 cold build ran capped
(490.65 s, peak RSS 4.17 GB, zero swap, 552 standard axiom reports). 261 modules
compiled; module 262 (`ExtractedDecoderCallerBridge`) failed:
`AspisR1TerminalDecoder.Types` and `AspisR1WithdrawalCaller.Types` both
generate the unqualified instance `instDiscriminantPoolV1TransitionKindU8`. The
arithmetic suffix passed separately (J10400–10402). This is the same shared
obstruction as release gate 1 (`IMPORT-UNION-20261021.md`: generated discriminant
instances take unqualified names, so separate extractions cannot be imported
together), and it has now blocked real work. Per AGENTS.md discipline §7 it is fixed
once, globally, before more privacy parts: adopt the prototyped
`<fully-qualified-enum>.instDiscriminant` naming adapter for every generated Types
module under `lean/` and rebuild the affected closures (capped). Session A's
`lean-candidates` get the same adapter and script through the handoff note rather than
lead edits. Privacy part 53 waits for it.

## D177 (user, 2026-10-23 01:05): lead decides for the next six hours

The user is unavailable until about 07:00 and delegated all decisions to the lead in
the meantime. Limits the lead keeps: no lowering of the security target, metric or
adversary; no change to frozen verifier bytes or the protocol; any new trust item is
named in the headline and logged with its reasons, so the user can reverse it; every
such decision is listed in a morning summary.

## D178 (lead, 2026-10-23 02:50): import-union fix merged (release gate 1)

Merged `codex/cx-import-union-20261022` (`evidence/import-union-20261022/summary.json`).
The prototyped adapter is promoted. 46 files and 130 generated discriminant
attributes under `lean/` are migrated to type-qualified instance names, with hash
manifests. 851 targets compiled, covering all 807 affected roots and consumers
plus the terminal bridge that blocked part 52. Release gate
`ImportUnionReleaseGate` (IU-1328): exit 0, 1.75 s, 4.59 GB, zero swap, 77
standard-only axiom audits. A census over 8,164 modules and 566,510 declarations
found zero duplicate definitions or instances; all 614 repeated theorem names have
identical types. Lead audit of the diff: no existing theorem statement changed (only
added helper lemmas and proof-script normalisations). Recorded separately: two unchanged
`AspisV8R19.SamplerWordRead` audits list the extraction opaque `core.fmt.Formatter`.
These are not in the frozen2 headline closure, but are to be eliminated or justified
before release. Not migrated: 56 `lean-candidates` files (session A's, with the script and
instructions in their handoff; the s126 S2 candidates are now the lead's and are migrated
when S2 imports them). The worker committed a 57.6 MB raw scan against the 5 MB rule;
it is replaced in the tree by its hash record (it remains in history).

## D179 (lead, 2026-10-23 04:30): part 53 merged; encoder via the owned route

Merged `codex/cx-prover-commit53-20261023` (two Codex capacity relaunches with WIP
snapshots; the final tree has no `sorry`). Proved: the migrated terminal-cone closure
audit; retained Poseidon callable and composition contracts; the retained terminal output
identified with the semantic terminal model; complete gamma batching; all three source
claim rows equal to the honest claims; stored Weights materialisation; composed opening cells
and ordered bytes; native `phi_inverse`. J10572: 30 modules, 59 standard-only reports.
Stopped on the shipped encoder (`encode_at`): its iterator adapters are opaque and body
extraction gives Charon trait errors. Direction, as in D144/D164: never extract shipped
iterator code. Write a D144-style owned encoder, then per-iteration Kani shipped = owned,
then Lean induction.

## D181 (lead, 2026-10-23 06:30): overnight summary for the user (decisions under D177)

Decisions taken by the lead overnight, each reversible by the user:
1. **S2 route B adopted** (C3-BIN 01:20): one new named trust item,
   `S2TrustedSdkBorrow`, covering the Solana SDK `AccountInfo` data-borrow semantics and the `RefCell` guard
   semantics in fifteen fields, pinned to solana-account-info 2.3.0. It is shown in the
   headline trust list. Its fields are proved mutually consistent, and its Kani spec is checked.
2. **Session A's S2 branch merged into research** (their handoff tip `0182d4eb4f`).
3. **Import-union naming fix applied to all of `lean/`** (D178, release gate 1). Session A's
   `lean-candidates` are untouched; they have the script. A 57.6 MB scan file was removed from the
   tree (it remains in history).
4. **Runtime abort and rollback** on allocation failure is to be stated under the existing runtime
   premises P2–P4 and checked against the pinned runtime (C3-BIN 02:40).
5. **S2 restructured depth-first** (C3-BIN 04:30), after five breadth jobs had not closed
   the native step simulation.
No security target, metric, adversary, protocol or verifier byte changed.
Status: S2 is open with 0/14 Required14 fields discharged. A large conditional
structure is proved (reference execution E for both stages, child value contracts, copy,
cleanup, error and rejection laws, return-data events, emitter constructor and indexed
writes). The native step simulation is at cut 1 of 30: the cut relation needed an
invocation binding, and that job is now running. Privacy: parts 53–54 proved the terminal, weights,
encoder and leaf bytes, and part 55 is running. Neither deployed target is established.

## D180 (lead, 2026-10-23 06:25): part 54 merged

Merged `codex/cx-prover-commit54-20261023` (report `r1p-final/PROVER-COMMIT54-20261023.md`;
budget J10600–10699 used). The owned encoder is extracted and proved by induction. Proved:
exact node geometry; encoder model identities; opened and folded leaf values with
ordered bytes. Kani verifies the actual M31/QM31/WideExact iterator transitions through
length 256 with verified stubs. 46 modules, 99 new theorems, standard axioms only.
Remaining before native simulator output = payload: native allocation/collection and
complete caller bindings; semantic guards; interpolation and challenge provenance.

## D182 (user decision, 2026-10-23 07:10): rewrite the adapter caller in a proof-friendly shape

The user asked why S2 had taken two days. Lead answer: S2 had been pursued as a proof that the
existing SDK-borrow-heavy adapter glue equals the model. Kani and Aeneas repeatedly
failed on that code (timeouts, translation errors, an internal Kani crash). Session A
spent about two days on SDK internals, and the lead's overnight jobs were too broad
and stopped at each first obstacle. S2-J did reach cuts 1–7 of 30 before stopping at
cut 8 (the verified SDK stub's descriptor bound excludes the real 1,768-byte buffer).
**User decision ("yes"):** rewrite stage 1 and stage 2 of `r1_pool_adapter.rs` in a
proof-friendly shape. Copy each account buffer into an owned value once at entry, run all
logic on owned values with no borrow guards held, and write the checkpoint back once at the
end. Then extract it with Aeneas directly. This is a verifier source change, so there will
be new ELF pins and a new freeze, with adoption gates; the extra compute units are
measured first and reported. Its accept/reject behaviour, outputs, checkpoint bytes and account effects must equal
the current adapter's. S2-J and S2-K were stopped. Their work is merged as
evidence: cuts 1–7, emit pieces and child contracts. Proved cones (checkpoint bytes,
multiproof, S7/S8, parser) are unaffected unless the rewrite touches their pinned
functions.

## D183 (lead, 2026-10-23 07:50): adapter rewrite: runtime-admission domain and error precedence

The rewrite's stage-1 note (`design/ADAPTER-RW-20261023.md`) shows that copy-then-drop
borrowing is not equivalent to the current adapter on the *raw SDK* input domain
(arbitrary borrow counters, distinct keys sharing a data cell, externally held borrows).
Lead ruling:
1. **Domain = runtime admission.** Equivalence is required on the inputs the Solana
   runtime can actually produce at the program entrypoint: each distinct account has its
   own freshly created data cell with borrow counter 0, no borrow is held outside the
   program, and duplicate account entries share a cell only when their keys are equal
   (rejected by the existing distinct-key check). This is a fact about the runtime's
   entrypoint deserialisation. It is stated as a named runtime premise beside P2–P4,
   checked against the pinned runtime/SDK entrypoint source, and not inferred from distinct keys or
   adapter acceptance. It does not restrict the adversary, who still chooses every
   account, key, owner, flag, length and byte of data.
2. **Accept set identical, errors may reorder.** On that domain the new adapter must
   accept exactly the transactions the old one accepts, with identical return data,
   checkpoint bytes and account effects. Rejection is rejection for soundness, so a
   different error code or precedence on a rejected input is allowed, but each
   difference must be listed. Where cheap, keep the original order (capture copy
   results, consume errors in source order).
3. **Resources:** the copies' heap use within the 256 KiB SBF bump heap and the CU cost
   are measured and gated. Allocation failure aborts the transaction (no effects).

## D184 (lead, 2026-10-23 09:10): part 55 merged; native Rust simulator binding stopped as unnecessary

Merged `codex/cx-prover-commit55-20261023` (about 0.87M tokens): the owned semantic oracle
with partial sums and interpolation; the original terminal and final semantic shift with
the successful guard; guarded encoders; opening challenge images; standard axioms.
**Lead finding (cost and scope).** Parts 46–55, and much of 30–33, bound the Rust
*simulator* `crates/aspis-r1-cost-probe/src/sim.rs` (`simE`/`sim_e_ablated`, "UNPROVED
COST PROBE", D44.3) to the model simulator. That serves only the *second* conjunct of
`RustProverRefinement` (rust.ideal = source.ideal). The simulator is a proof device that
is never deployed. Deployed privacy is a statement about the real prover's observable
output: its distribution is within ε of the ideal game run with the mathematical simulator
`simE`, whose efficiency is a property of `simE` (the SIM-COST passes, D116–D142). So the
deployed headline needs only rust.real = source.real (conjunct 1) plus the model theorem
source.real ≈ source.ideal. Restating the deployed endpoint as
"rust.real ≈ source.ideal(simE)" is the same claim about deployed outputs, not a
weakening. Before/after statements are to be shown verbatim in the restating job.
Consequences: native `sim.rs` binding work stops (its results stay as evidence); privacy work
goes to the real side (`prove_masked_retrying_with` and the prover, on the v2 candidate
code paths where they differ), plus the L1/L2 side-channel obligations.

## D185 (lead, 2026-10-23 09:15): privacy comparison contract is the mathematical simulator

The restatement job (`r1p-final/PRIVACY-RESTATE-20261023.md`) correctly stopped. The
existing deployed conclusion compares rust.real with `rust.ideal`, the ideal game run by a
Rust implementation. The proposed one compares rust.real with `source.ideal(simE)`. As
fixed-experiment propositions they differ, so this is a contract choice, not a proof step.
**Lead ruling (logged for the user, reversible).** The privacy contract is the standard
simulation definition: for every adversary, the deployed real experiment is within ε of the
ideal game run with the efficient mathematical simulator `simE`, whose cost bound is proved
for `simE` itself (the SIM-COST passes). The old conclusion together with conjunct 2 implies the
new one; the old is stronger only in additionally certifying a Rust implementation of the
simulator, which is never deployed and says nothing more about deployed outputs. The
previous theorem is kept unchanged; the new endpoint is added beside it with before/after statements.
Privacy work proceeds on conjunct 1 (the real side) using the worker's obligation map.

## D186 (lead, 2026-10-23 09:25): real-side privacy endpoint proved; real-prover refinement plan

Merged `codex/cx-priv-restate-20261023`. `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed`
is proved from conjunct 1 alone. It compares deployed `rust.real` with `source.ideal(simE)`,
with the same error envelope (J10800, standard axioms). The old theorems are unchanged.
Lead assessment from the obligation map (`PRIVACY-RESTATE-20261023.md`): most of parts 27–55 bound
simulator code or proved shared helpers. The native refinement of the **real** prover
(`generate_for_mask_nonce` → `prove_masked_retrying_with` → prover.rs: masks, semantic
build, commitments/Merkle, transcript/sumcheck, opening, publication) is largely
unstarted as a whole, though many helper results transfer. Plan: three parallel
depth-first streams, each budgeted and using the routes that work (D144 owned references,
per-iteration Kani shipped = owned, Lean induction; never Aeneas on shipped iterator code):
R1 the retry/entropy/reservation owner on the selected caller (composing parts 34–43); R2 the
real commitment path (mask material, semantic build, commitments, Merkle, encoding); R3 the
real transcript, sumcheck, opening and publication. All target the research prover. The v2
candidate's differences transfer through its proved equivalence gates when it is adopted.

## D187 (user decision, 2026-10-23 11:05): proof-friendly prover rewrite

Real-prover refinement streams R1–R3 (merged): a host proof-account caller on the 64-byte
route with a durable ledger, where duplicate nonces fail closed and the verifier ELFs are unchanged; native/owned
control binding and an outer-owner bridge; mask-seed guards and context framing; transcript
rows 0–14 by reused part-30 callee contracts. Each stream stalled on Kani timeouts over shipped
prover loops (R2 at the scalar sampler contract, R3 at row 15), the same pattern S2 had before
the adapter rewrite. R1's +27% caller timing is from a contended shared host and will be
re-measured on a quiet host. **User decision:** rewrite the prover's control and per-attempt
pipeline (retry owner, mask material, semantic build, transcript, commitments, publication)
into owned, Aeneas-extractable code, with heavy arithmetic as small verified leaf kernels.
Base it on the v2 constant-time candidate, which is the intended host prover. Gates: design
note first; byte-identical proofs on fixtures for identical coins; at least 1,000 differential runs;
median prover time under 15 s on the build host (D168/D169); the verifier untouched. Host-only.

## D188 (lead, 2026-10-23 16:40): what "native" means for extracted code (S2 closure ruling)

S2-W keeps listing a residual "native-to-owned association" for code that Aeneas has
already extracted. Lead ruling: the project's source semantics are the Charon/Aeneas
extractions, as for every soundness cone (S1–S10, checkpoint, multiproof). Correspondence
between Rust source and its extraction is the existing extraction trust boundary (named
`AeneasExtraction`, beside rustc/P7). Correspondence between source and the deployed binary
is S10's ELF certificates plus P7. So for the extracted owned adapter, "native = extracted"
is not a new S2 obligation, and no per-call re-proof is needed. What S2 must still prove:
(i) the non-extracted wrappers, by their Kani contracts, which pass; (ii) composition of
the traced outer execution. Child-internal site events (verifier stage internals, the nine
internal sites) belong to the child cones and are carried as the named per-child cone-join
hypotheses. Multiproof's separate P6 total-oracle premise stays with the multiproof cone. With
this, the consolidated `S2CallerFacts` theorem should be statable. `AeneasExtraction` is added
to the headline trust list explicitly; it has always been implicit in every cone.

## D189 (lead, 2026-10-23 17:35): S2: the native AccountInfo ↔ heap association is the trust item's job

S2-W composed every field at the interpreted heap boundary: `callOrder`/`reachedPrefix`
by flatMap over the outer log; returned vector → write → checkpoint version; full account
frame and metadata. It stops at identifying native `AccountInfo` wrapper pre/post states
with the interpreted heap. Lead ruling: that identification is exactly what
`S2TrustedSdkBorrow` supplies. Its fields `account_data_cell`, `cell_payload`, `cell_counter`
and `borrow_frame` *are* the explicit trusted relation between the actual typed Rust carrier
and the abstract heap (plan, route B; C3-BIN 01:20), and the wrapper Kani contracts check the
native wrapper code against it. Vec snapshot allocation and cleanup are TrustedStd plus the
runtime allocator premise (allocation failure aborts the transaction). Child frames are empty on account
state because the owned design passes children only owned values and never an
`AccountInfo`. This is to be proved from the extracted signatures, not assumed. With these, the full
`S2CallerFacts` theorem follows. No new assumption is introduced. These are the existing items,
used for their stated purpose.


## D190 (lead, 2026-10-24 10:55): entropy interpretation obstruction retained

The unmerged prover candidate at `7db89a0216` proves
`ProverRwEntropyIteration.no_retry_then_success`: a fixed pure external
getrandom.fill dictionary cannot produce a retry followed by success on the
same freshly zeroed buffer. Native E1 admits a zero draw followed by a nonzero
draw. The lead inspected that theorem and `no_two_draw_dictionary`; this is a
real obstruction to the proposed fixed-tape refinement, not a privacy attack.
Do not hide the false equality inside PrefixContract or BodyContract.

Authorize a proof/tooling-only effect-aware entropy interpretation carrying
an explicit tape cursor/world state through the actual entropy and retry owner.
Preserve every draw, errors, exhaustion, the unchanged bad-event probability
law, and joint L1/L2 observations. A hand-written stateful model alone is not
source refinement: connect it to the pinned source/emission with a checked
transformation or a proved sufficient observational transport. No new extraction
trust, RNG assumption, source change or security-contract change is authorized.
If existing tools cannot support this without new trust, report the smallest
concrete decision and its consequences. The zero-then-nonzero counterexample
remains a regression obligation.

The candidate's sampler/retry/salt helper results remain conditional on its
uninstalled external dictionary (260 function entries and 28 type carriers).
Audit 11261 passed in worker evidence: exit 0, 1.69 s, peak 4,266,180 KiB RSS,
swap 0, source revision d735d8174e plus exact source hashes, standard axioms.
This evidence is reused, not independently replayed; no candidate adoption or
release proof is claimed. Stage-3 budget used 60/100 Lean and 42/60 Kani;
continuation has 40 Lean and 18 Kani remaining, IDs beginning 11262 through
11399 subject to collision checks. Absolute quiet-host timing remains open.
See candidate `design/PROVER-RW-20261024-STAGE3-CONTINUATION.md`.


## D191 (lead, 2026-10-24 11:29 UK): effect packet reviewed; explicit entropy plumbing preflight

Candidate `748e710252` retains the fixed-pure-dictionary obstruction and adds
checked factoring of the emitted entropy owner. `ProverRwEffectOwner.pure_owner_eq`
and `ProverRwEffectRetry.client_retry` connect only the PURE specialization to
the emitted owner/callback. `owner_zero_then_one` proves the separate world
interpreter's two-read regression. The lead inspected these complete statements:
there is no native worldOwner equality or E1/L1/L2 transport theorem. The pinned
backend inspection finds no implemented implicit-world extraction option.

Read-only final-source/receipt/axiom checks pass. Worker audit 11288: exit 0,
1.80 s, RSS 4,264,628 KiB, swap 0, source 45e27024aa and exact hashes, standard
axioms. No new shipped changes or derived files over 5 MB. This remains on the
unmerged adoption candidate. Existing evidence was reused; no proof replay,
new native identity, privacy closure or new trust item is accepted.

D187 already authorizes a proof-friendly host prover rewrite as a gated
candidate. Within that scope, authorize an explicit entropy-state/coin-provider
interface in the HOST candidate, after a committed design and extraction
preflight. Preserve actual OS draw order and count, nonce rejection, entropy
error mapping, zero-buffer/zeroization behaviour, cap16 and outer retry behaviour,
including errors. State must actually distinguish successive calls and be
threaded across the complete retry owner; a constant ghost token or a reset
cursor cannot stand in for fresh effects. The native OS leaf must remain tied
to the exact existing E1 boundary; do not assume a whole-owner equivalence,
introduce new freshness/trust, or rename a missing source proof as an assumption.
The fixed-tape coupling must use the same event sequence, not merely equal
successful outputs. If this cannot be justified under the existing boundary,
stop the dependent source change with a concrete minimal decision for review.

First align the candidate with the already-approved H5 source change from
research. Any host refactor remains UNADOPTED pending source/effect equivalence,
relevant differential and L1/L2 gates, all three current ELF identities, and
quiet-host <15 s plus <=10% slowdown. Never change frozen verifier bytes or
adopt a backend patch/new extraction trust. Preserve all historical source and
counterexample evidence. Stage-3 budget is 84/100 Lean and 42/60 Kani used;
this preflight gets only the remaining 16 Lean and 18 Kani, IDs starting11289
through11399 subject to used-ID checks. A broader follow-up needs lead review
of this concrete preflight, not an unannounced budget reset.


## D192 — explicit entropy preflight reviewed; cap16 source gate next (2026-10-24)

Candidate ece5baabbc remains unmerged. The source-derived owned Draw64
prototype is extracted with real changing provider state; concrete_zero_then_one
consumes two entries from one finite Tape and returns cursor2. Error and cap
control preserve provider state. Four final module hashes and nine standard
axiom reports were checked; audit11305 at ddb833a1cd exited0,wall2.14s,
RSS3873112KiB,swap0. Same-event runtime coverage is26214 LOCAL entropy-helper
cases, and Kani proves an arbitrary-input ONE-iteration source cut only.
Neither establishes universal cap16 or cap8/native event correspondence.
No crates/programs change against H5 base71100fccbd; no ELF/timing rerun.

E1/E2, native error-carrier association, physical cleanup, callback/retry and
joint L1/L2 transport remain undischarged. Generated Emission carries explicit
heartbeat/recursion defaults; the next stage must remove them in adaptation
and validate the affected closure under default options. No limit increase is
authorized. This is a proof-configuration cleanup, not a rejected mathematical
claim or permission to substitute a model theorem for native refinement.

Stage3 consumed100/100 Lean and44/60 Kani. After review, authorize a separate
bounded continuation of60 NEW Lean attempts for universal cap16 same-event
source-owner induction; retain only16 unused Kani runs and both old/new
ledgers. This stage changes isolated prototypes/proofs only; native plumbing
follows its predecessor gate. Scope/prompt is archived under
 evidence/coordinator-20261024/prompt-prover-rng-owner-20261024.txt.
No security target, contract, native source, trust or candidate adoption changes.


## D193 — universal source-derived cap16 gate reviewed (2026-10-24)

Candidate03444c5e5e remains unmerged. universal_cap16 quantifies over arbitrary
nonces and typed finite tapes, proving both complete owner equality and shared
body-state replay with exact consumed reply order/count, fresh zero inputs,
available indices, returned status/provider and final suffix. Its admitted
.ok execution includes native-prototype OS/exhaustion errors; tape unavailability
stays extraction failure. It is stronger than the prior zero-then-one example.
Replay/OwnerReplay and concrete body/loop proof were inspected; they do not hide
old/new owner equality in a premise. The Kani cut is not a Lean hypothesis.

Lead checked14 final matching-source green receipts, default-option cleanup
and22 standard-axiom reports. Audit11439 at ad9e91a840067eae7a44e8ab7f103b0e59b24698:
exit0,wall1.79s,RSS3847484KiB,swap0. Independently reran binding-audit read-only
against LLBCcfb6f9bec8a6d002ed6f1e141649334256af3d17d7837b27cbd811ddeedc364d:
eight transparent local declarations,13 identical shared definitions and actual
source substitutions checked. No new full-manifest/native identity gate.

Native getrandom::Error/E1 association, physical cleanup, selected callback,
cap8 owner, durable ledger and joint L1/L2 remain open. No crates/programs delta
in this stage. Next source-derived prototype task targets the actual native
error carrier plus RealR1_client callback and retry_attempt, preserving all
mutable provider/nonce-policy state and failed/rejected effects. It may use only
20 remaining Lean from the60 owner allocation and16 unused Kani; stage3 stays
100 exhausted and cumulative usage140/160. No budget reset, new trust, contract
change or native adoption. Archived prompt is
 evidence/coordinator-20261024/prompt-prover-rng-caller-20261024.txt.


## D194 — Callback/cap8 prototype review and native producer continuation (2026-10-24)

Candidate abbee7673d remains unmerged/unadopted. ProverRwRngCallerReplay.replay_complete/replay_sound and cap8 establish concrete emitted retry-step execution and at most8 callbacks for admitted prototype runs; Events.callback_invocation preserves actual mutable policy state and ordered_indices fixes trace indices. Composition.zero_reject_fatal connects three fresh zero64 fills through entropy rejection, body rejection, then fatal Semantic, retaining advanced provider/policy/store/body state. These local premises are exact policy/fill/body calls, not whole-owner equivalence.

Lead inspected complete Replay/composition and hidden NativeTypes/Body boundaries described in design/PROVER-RW-20261024-RNG-CALLER.md. Independent bind.py --check passed (source map SHA256910680a1d6733b7faa3a5631910de8a384d81e0395ca7850a087a6c065345842); step-cut.py passed (96ef867805cc7d0941a0964e3ab070218ed6e32df47bb3a425b25ebde492d7a5). All8 final module source hashes match accepted receipts; final audit11459 on f3e9539784e1ec5fb2606db12fdd4564cc13d80e recorded exit0,2.68s,RSS3846700KiB,swap0,27 standard-axiom reports. Lead reused compilation evidence, no replay.20/20 new launches consumed; prior100/100 and owner60/60 exhausted, cumulative160. Kani44/60 unchanged.

Native closure is NOT established: core nonzero-I32 TPattern extraction fails; NativeTypes remains uninstalled; universal native-error cap16 transport is missing. Body is an owned-store abstraction after borrowed FnMut emission mismatch; u64 audit substitutes for MaskedFixtureAudit. Actual reservation/build producer, exact native input/status/events, physical cleanup, bytes/context-to-Raw and L1/L2 remain open. Prototype zeroize1.9.1 differs from native1.8.1. E1 is unchanged. No native source delta, ELF or performance gate.

Lead explicitly allocates new60 Lean attempts (cumulative ceiling220, prior160 retained), with only16 remaining Kani, to ProverRwRngNative. First align dependencies and prove sufficient source error abstraction at selected map_err, without new trust/backend changes; then bind actual reservation/build and audit/control producer. No shipped-source changes authorized in this stage. Full task archived evidence/coordinator-20261024/prompt-prover-rng-native-20261024.txt. Worker PID57141; exact output in scratchpad codex-prover-rng-native-20261024.out. Target not yet established.


## D195 — Actual reservation source review and material producer continuation (2026-10-24)

Candidate dbc123fdc8 stays unmerged. Proof5296e55148dcf6687afaef878a5ef9e872b9a160 establishes selected_duplicate_fatal/selected_io_failure on actual emitted prove_masked_attempt with native MaskedFixtureAudit/borrowed-store types. Named public serialization, exact hash/context and filesystem/classification replies remain. reserve_fallible is an UNPROVED filesystem component (path/hash/allocation/create_new/write/fsync/directorysync), not discharged by adapter control. reservation_invariant preserves post-reservation store for every admitted suffix and requires successful material results to traverse explicit clear leaf; physical erasure remains open.

Lead read complete Producer/BuildControl/BuildPaths/ReservationInvariant and TypeLeaves/LocalLeaves boundaries. Independent bind-body004--check binds134 declarations/29files; adapt-body--check passes. All23 summary source hashes and10final greenmodule receipt hashes match. Audit11523 reused:exit0,1.26s,RSS2631692KiB,swap0,19standardreports. No replay/fullmanifest/nativeartifact/perfgate. Prototype now zeroize1.8.1/getrandom0.3.4. Native entropy sort/result/destruction transport, opaque16sorts/35leaves installation, cap8 body/audit/event binding, successfulbytes/context->Raw,E1association,physicalcleanup,L1/L2 remain open. Hostprefix file difference is retained source assessment:28wholefiles match, all referenced spans in29thmatch literally. No shippedsource delta.

Used24/60 newLean; prior160 retained,cumulative184/220;36remaining. Kani44/60 unchanged. Worker67242 now consumes ONLY36remaining on actual materialgenerator acknowledgment/derivation control and its reservationconsumer, then actual callerbinding if feasible. No newtrust/backendpatch/sourceadoption. Prompt archived evidence/coordinator-20261024/prompt-prover-rng-material-20261024.txt. Both targets notyetestablished.


## D196 — Material producer and borrowed caller reviewed (2026-10-24)

Candidate067e1ddd1e remains unmerged. Proofc88daf1e50bec23f1d1425b33a4820ce963ddc7d: material_success_ack derives usedAck and context nonce for all admitted material successes; layout_post retains exact reserved store across all admitted sampler outcomes. reserve_sample_success constructs reservedsecrets/material from four ordered sampler replies plus named source leaves. selected_zero_entropy/selected_sampling_failure discharge prior whole-material result premises in concrete source paths. Actual borrowed cap8 selected_sampling_retry threads advanced callback/store; selected_zero_fatal aborts; last_sampling_exhausted atindex7 returns AttemptsExhausted. Structural body_success still assumes actual body success. No native entropycallback/runtime/oldBody instantiation follows.

Lead read complete claimed statements/hidden source interfaces. Independently bind003--check (164declarations/30files) and adapt--check passed;13currentmodule hashes match greenreceipts;38standardaxiom audit reports retained. Audit11550 reused:exit0,1.42s,RSS2631356KiB,swap0. Source/dependency checks reused with explicit cachedsource assessment; no fullmanifest/artifact/runtime/perfgate. Layout/four sampler components,16opaque sorts/41localinterfaces, filesystemcomponent, successful fullbody, physicalcleanup, bytes/context->Raw,E1association,L1/L2 remainopen.

27newattempts used,211/220cumulative;9remain. Kani44/60unchanged. Worker74207 consumes ONLY9remaining for precise getrandomNonZeroI32 source representation/result/destruction transport preflight, or concrete minimal proposal if existing pinnedtrust cannot support it. Archived Copy-derived Error may support a valid-subtype route: this is a lead inference to test, not an installedrepresentation. No backendpatch/newtrust/shippedsource authorized. Prompt archived evidence/coordinator-20261024/prompt-prover-rng-transport-20261024.txt. Both deployedtargets notyetestablished.


## D197 — Error representation review; selected adapter correction (2026-10-24)

Reviewed a684b31c35, theorem source76e1dd33405524d0bc072f4d98e4959c96053777. ProverRwRngTransportValidity proves exact archived I32 range-pattern iff nonzero, value preservation and inverse subtype maps. It supplies no native representation or operation association. Both11551/11552 hashes match green receipts; four standard reports each;5G/7G,no swap,shared lock. No native premise discharged. Cumulative213/220 Lean used,7remain;Kani44/60 unchanged.

Correction: proposal requirement3 selects alternate prover::prove_masked_retrying/96-byte generate() as actual secure factory. This conflicts with D152 and the selected release path. Authoritative target remains RealR1_client::prove_for_proof_accounts -> generate_for_mask_nonce(proof_account(k)),64 private bytes plus public adaptive nonce. The96-byte API is outside that adapter. Current source confirms both distinct APIs. This is a reporting/next-task correction, not a protocol or target change; all prior local control results retain their documented scope. E1 unchanged.

Lead authorizes an isolated unadopted extractor candidate for the exact refined-I32 pattern under the existing AeneasExtraction boundary. No shared/installed tools, shipped source, trust, frozen verifier or protocol change. Must pin/reproduce existing extensions plus patch, preserve validity/type identity and move/Copy/disposal semantics, fail closed on unsupported cases, and extract ACTUAL selected64-byte closure before native claims. Worker77049,7remaining Lean,12 extraction and4 backend build attempts maximum. Prompt archived evidence/coordinator-20261024/prompt-prover-rng-extractor-20261024.txt. Feature adoption requires review. No ELF/runtime/perf claim. Both targets notyetestablished.


## D198 — Isolated extractor packet reviewed; bounded repair (2026-10-24)

Reviewed3747025cbf. Selected source correction96f7984a59 preserves the64-byte RealR1_client route. Candidate003 built and translated synthetic wrap/map_err/move/Copy/disposal; actualselected64 Charon extraction passed. Native operation association and matrix/Lean validation remain open. Candidate003 normalized outer records to aliases; candidate004 attempted preservation but failed on opaque Disambiguator.id matched as raw0. Its source is distinct from successful003binary09af4fe5a40f2340b3b326e01b15b23d8e8a0a39e3ae25938f9033dd56d5fdc5. No source004binary claim.

Lead inspected exact pattern recognizer, refined puretype,scalaroperation guards and recordpreservation patch; independently checked all7 receipt hashes/statuses and zero swap. Source/patch manifests and pinned compiler recipe are retained. No new native assumption discharged, installed/shared tool changed or source/runtime/artifact/performance gate claimed. Current OSfill interface still lacks explicit provider/event state; toolfeature alone cannot close that boundary.

Builds4/4 exhausted; lead explicitly allocates4additional attempts005–008 (cumulative ceiling8), preserving previous failures. Extraction3/12used,9remaining;Lean213/220used,7remaining;Kani44/60unchanged. Worker85279 repairs IDmatching then validates retained records,selected operations/negativecases and actual64Aeneas/Lean output. No adoption/newtrust/shippedsource authorization. Prompt archived evidence/coordinator-20261024/prompt-prover-rng-extractor-resume-20261024.txt. Bothdeployedtargets notyetestablished.


## D199 — Extractor counterexamples and native path strategy (2026-10-24)

Reviewed57e7c88e14/localproofbb9ec678e2. Lead inspected complete Operations source and actual Drop probe/output. Four final source hashes match green receipts;14standard reports audited at11558 (exit0,1.07s,RSS2622428KiB,swap0). Candidate005 preserves typedrecords and local From/map_err/disposal algebra; fullselected64 fails borrowedFnOnce/FnMut signatures/traitdefault. Drop probe's Guard increments counter but emitted real_drop returns unchangedcounter, despite overall translationfailure. Candidate007 rejects structuredDrop/escapingreferences beforeemission, includingactualcrate. Neithercandidate accepted; no native premise discharged. Preserve regression and partialoutputrejection. Baseline withoutrefinederror still needs its own probe beforegeneralizing installedtool claim.

Resource correction: reused aggregate scanner omitted system.slice Docker scopes. Individualcaps/swapreceipts remain; historical complete aggregate<55GiB is unverified and cannot be repaired posthoc. Lead current all-scope hierarchical finite reservation check found24.375GiB includingDocker/services; current observation only. New worker must fix/test job-owned admission scanner before heavylaunch and must not affect unrelatedservices.

Oldbuild7/8,extraction12/12,Lean219/220,Kani44/60. Lead allocates4newbackendbuilds (5available,ceiling12),12newextractions (ceiling24),40newLean (41available,ceiling260);alloldledgers retained. Worker93315 owns committed safe source/extractor design and gated actual64-byte ownedprovider/control path under D187/D191, preservingcleanup/events/errors/ledger and unchangedE1. No installedtool/protocol/frozenverifier/trust adoption. Any nativecandidate source change requires full3ELF/differential/refinement/performance gates before adoption; no sourcegate claimed. Prompt archived evidence/coordinator-20261024/prompt-prover-native-entropy-20261024.txt. Both deployedtargets notyetestablished.


## D200 — Native Drop probes retained; complete output still fails (lead, 2026-10-24)

Reviewed unmerged provercandidate80a4a07181/aeec7331d8, native-entropy REPORT/design. Optimized five Guard probes give0->1; pinned baseline translations020/022 exit0 yet emit identity real_drop. Whole020 emission fails Lean11560 on borrowed Option.take return shape;022 remains uncompiled, swap signature mismatch observed. No kernel-accepted baseline counterexample or general installed-backend unsoundness claim. Candidate007 actually rejects minimal and selected64 beforeoutput. No native refinement/E1/source premise discharged. Candidate stays unmerged; no shipped/installed tool change or new trust.

Lead read actual probe/output/diagnostics/interpreter Drop branch and complete structural/audit sources; independent read-only collector/source association,187integrityhashes,11scanner+3Dockerbarrierfixtures passed. All12extractions+4Lean receipts retain exacthashes/commands/caps/swap; audit11562 ataeec7331d8+native-entropy-drop-probe exit0,1.03s,RSS2621948KiB,swap0,three no-axiom structural/library reports. This is interface inspection only, not source theorem. Lead found generated heartbeat/recursion defaults in new structural Types; nextworker must remove them and recompile changedTypes/dependentaudit, preserving oldhashes as historical. No claim of whole-source closure. Historical completeaggregate remains unverified; current hierarchicalscanner/barriers reviewed.

Budget backend7/12,Lean223/260,Kani44/60. Lead allocates12newextracts after24/24 exhaustion, ceiling36. Nextnative-drop worker designs and attempts realdrop_glue/loan handling, complete kernel-accepted Guard regression then actualZeroizing; no owned-wrapper substitute over unresolvedcleanup, noinstalledtooladoption. Both deployedtargets notyetestablished.


## D201 — Actual drop-glue emission remains unaccepted; baseline flag correction (lead, 2026-10-24)

Reviewed unmergedcandidatec42a29bc58 (37cc3cf769/69d404c658/c24fc5da9f). Generatedlimitsremoved and correctedTypes/dependentaudit recompiled. Candidate012 preservesregularpreciseglue and emitsactualcall, but WHOLEGuard11566 fails borrowedstdlibpair/tripleABI and generatedok-matchtyping/syntax. No destructorrefinement/counter0->1kernelresult/sourceorE1premisedischarged. CompleteunchangednoDropincrementclosure passes,notcleanupsemantics. Selected64andactualescape/capture035rejectbeforeoutput;031onlylegacymutatedLLBC,notnativeescapeevidence. Candidateandinstalledtoolremainseparate,noadoption.

CORRECTION toD200/baseline20/22metadata: exactpinnedConfigdefaultdrop_as_no_op=true;commandsomit-eval-drops. Priorlabelsfalse/claims thatthosecommands exercised drop_value are unsupported. Their omittedDrop effects areconsistentwiththeno-opdefault. Staticnon-no-opbranchignoringfn_ptrremainsexactsourceobservation,not executionevidenceforthosecommands. Nocompletekernelacceptedbaselinecounterexampleorbroadinstalledtoolunsoundnessclaimfollows. Oldreceipts retainedhistorically.

Leadreadsourcepatch/design/fullacceptedTypes/noDrop/audits/rawGuarderrors/flags;independentread-onlycollectorand223integrityhashespass. Backend008pre-gomissingbarrierfailurecharged,compilerRSS/swap/timeunavailable;remainingcompilers/extractorscappedandmeasuredswap0. Audit11569atc24fc5da9f+candidate012 exactsource/dephashes exit0,1.07s,RSS2622024KiB,swap0,standardfourreports(incrementstandardthree;Guard/take/swapnone). Cached/localproofscopeonly,noELF/performance/frozenreplay. Historicalfullaggregateunverifiedunchanged.

Budgetbackend12/12,extraction35/36,Lean230/260,Kani44/60. Leadallocates4backendbuilds ceiling16 and8extracts ceiling44(9available);Lean30remaining/Kani16unchanged. NextisolatedABI/printerworker mustderivecompleteforward/backwardloaninterface,repairsourcebackend,thenwholeGuardkernelregression. No extra-tupleslot/handwrittenoutput/newcleanupaxiom. Bothdeployedtargetsnotyetestablished.


## D202 — Selected64 client candidate passes offline source review; adoption remains gated (lead, 2026-10-24)

Reviewed unmergedclientcandidate1dfbd5711684,after4aac77a772/a5ec23f4f653 and nestedlistingfix. Actualplanner calls unchangedRealR1_client::prove_for_proof_accounts with8validatedretainedkeys;actualsuccessfulattemptkey/indexfeedsstage1/settlement/create/upload. Pythonpersistedprivateclaim/manifestandartifactmappingrefusesreproofafterfatal/error/ambiguousinterruption,retainsallrejected/unused/stagingkeys,validatesresumeandauxiliarykeys. Inventorynowincludesnewnestedkey/recoverypathswithlegacy/partialcoexistence,known/configuredscope,publicpathrecords,querydedup/batches<=100andfailclosedmissing/symlink/mode/listingerrors. Leadfoundbothinitialinventoryomissionandnestedos.walksilenterror;regressionsretainedandfixed. No cleanup/keyoperation/chainexecutionran.

Leadreadallproductionhelpers/wiring/actualtests andmatched21finalsource/dependencyhashes,56packetchecksums,unchangedcurrentRust03sources/caps/admissionsandhistorical16lifecycletests. Python13reproduced8listingfailures;Python14final15inventorytests+sourceaudit exit0,2.62s,RSS100139008bytes,swap0 atfa06e9bcfd+exactdirtyhashes. Rust03actualplanner2tinypublicJSON/accountselectiontests exit0,0.5125834890059195s,RSS222828KiB,swap0;release/locked/offline,j4,6G8GnoSwapTasks64. Rust/16lifecycleevidencereusedbyexactunchangedsourcehashes,notrerun. No proofgeneration/nativeprivacy/cleanup/refinement/ELF/performancegateclaimed. Pythonbudget14/14,Rust2/4,allformal/extraction/backend0.

CandidatekeptUNMERGED/UNADOPTEDwithcleanworktreecodex/cx-client64-20261024,notdeleted. Source/artifact/selectednativeproof/refinement/E1/L1/L2/CTv2andquiet<15s/H5<=10%gatesremain;developmentrootstillhasoldgenericcalleruntiladoption. No crates/programs/shippedverifier/trust/contractchange. HistoricalELFpinsreusedonly. Nextintegrationusesreviewedclientcandidatewithfinalnativeproversource,thenapplicablegates;noredundantreplaywhileupstreamsourcechanges. Bothdeployedtargetsnotyetestablished.


## D203 — Printer repair retained; actual owned cleanup is the next source class (lead, 2026-10-24)

Reviewedunmergedprovercandidateb724680f27/60e19e18a4/78a5893610. Candidate015sourceprinterparenthesizesargument-positionLeanmatch/if;actualunchangedGuard11574losesthreeprintererrorsbutSTILLfailsnested-swappair/tripleABI. Candidate013move-loweringfailsCouldNotReadBorrow;twonoDropborrowprobesfailmutable-borrowcopy. Candidate014rejectsgapsonselected64/escape/capture;itsnewnestedguardnotseparatelyexercised. No actualtypedloan/destructor/counter0->1/native/E1premisedischarged. StructuralpermutationlemmasarenotAeneascontext/loanendingrelations. Earlier020/022defaultflagcorrectionretained. Onefailedv1probeLLBCwasoverwritten;exacthash/Rust/logssurvive,notfullinputbytes. Noadoption/sourceclosureclaimfromit.

Leadreadactualdesign/report/structuralproofs/collectorsandindependentlychecked18receiptrows/exportedintegrityandbyte-identicalnoDropdeclaration,allmeasuredswap0. Audit11575at78a5893610+typed-relation exactsource/dephashes exit0,1.09s,RSS2623016KiB,swap0;8reportsstandard(incrementthreeaxioms,othersnone),notbrokenGuardimport. Cachedfocused/localhelpervalidationonly,noELF/performance/frozenmanifest/toolinstallation. Budgetsbackend15/16,extraction44/44,Lean236/260,Kani44/60.

METHODCORRECTION: genericnestedGuardregressionwaslead-imposeddiagnostic,notauserreleaseobligation. ActualZeroizing32/64ownsbyteswithoutnestedreferenceT. LeadrevokesblanketGuard-firstprerequisiteandassignsworker17730actualselected64Drop/captureinventory,actualowned-arraycleanupsourceproof/existingP6-KanirouteandweakestSUFFICIENTtransport;arbitrarypublicpolicy/cleanup/error/trace/loansstillrequiredwhereactualexecutionneeds them. UnsupportedgenericGuard/toolclassesremainunaccepted/failclosed;nosecurityscope/adversaryweakeningornewtrustedcleanupaxiom. Noanotherstructuralwrapperasnativeclosure.

Leadallocates4newextractionsceiling48;backend1remaining/Lean24remaining/Kani16remainingunchanged,max8Kani+4optimizedRustchecks inthisstep. ExistingD187/D191actualsourcecandidate/gatesapply;anynativechangesmustpassall3ELFs,fixedcoin1000,nativeevents/refinement,H5<=10%,quiet<15beforeadoption. Actualselected64nativeowner/E1/L1/L2/L3/sourceartifactandbothdeployedtargetsremainunestablished. Clientcandidate1dfbd5711684staysclean/parked/unadopted. Promptsarchived.


## D204 — Actual zeroize32/64 component checked under Kani; caller transport remains open (lead, 2026-10-24)

Reviewedunmergedprovercandidate3e136e21b9/588db5d759 actualharness/report/receipts/sourceaudits. SixuniversalKanipassesexecuteunchangedzeroize1.8.1arrayZeroizeandactualexactly-onceZeroizingdestructionfor32/64. Stronger049/050moveowners,derivepayloadoffsetwhilelive,dropactualowneronce,reacquirefreshrootpointerfromliveMaybeUninitbacking,checkzeroONLYinitializedpayloadandtwoarbitrary16-byteframes. Earlier047/048child-pointerobservationsremainKani-model-only/supersededforlifetimereasoning. No freedallocation/doubledestruction/layoutassumption/expectedzeroassume/destructorstub. ThisisKani sequentialpayload/frameevidencewithSOURCE-INSPECTEDlifetimeargument,NOTmechanizedRustprovenance/nativehardwareerasure/callerinvocation/order/source-trace/wholeownerclosure. No promisetoeraseoldmovedcopies/registers/caches. AtomicfenceissequentialinKani;unsupportedforeignpathsretainenabledfailurechecks.

Independentread-onlysummary/sourceassessmentmatches10checks+2postaudits,alladmissions/6G8GnoSwapTasks64andmeasuredswap0. Kani049exit0,2.3216904409928247s,RSS147580KiB;050exit0,4.65774834700278s,RSS203564KiB,exactsources/solver/compilerpinspreflight/go. NoLeanemission/compilation/axiomclaim. Charon045/047succeedbutAeneas046/048rejectbeforeoutputonIterMutreturningmutable refsandprojected/traitDrop. Concrete-onlymonomorphizedgraphuntested. MissingpreflightCharon/shimbinarypinsareexplicitpostrun-onlylimitation,noretroactiveidentitygate. GenericGuardfailuresremainunaccepted. Allnative/refinement/E1theoremstatementsunchanged;wholeownerpremisesnotdischarged.

Budgetbackend15/16,extraction48/48,Lean236/260,Kani50/60;thisstep6/8Kani,0/4Rustchecks. Worker25873nextprovesactualgenerate_for_mask_noncefactorynormalcontrol/error/moverelationunderarbitraryOSfillprimitiveoutcomesandbindsactualcleanupsitesunderexistingP6wherejustified. NoEntropy/OSuniformity/E1probabilityclaimfromstubs;noDropstub/eventloggerwithoutsource-erasure/contractproof. Unwind/captures/outer8/ledger/publicpolicyremainrequiredseparateobligations. Leadallocates4newextractionsceiling52;max4remaining10Kaniforthisstep,max2optimizedRustchecks;backend1/Lean24remainunchanged. No sourceadoption/3ELF/performance/frozenmanifestgate. Bothdeployedtargetsnotyetestablished.


## D205 — Factory first-path relations checked; full retry composition remains open (lead, 2026-10-24)

Reviewed unmerged prover candidate745f551f84 and its actual included source, Kani harness, cleanup association and receipts. Kani051 proves zero public nonce returns RepeatedZeroBlock without drawing. Kani054 proves arbitrary nonce with a first-fill Err: a nonzero nonce enters exactly one fresh-zero64 draw, arbitrary64 postbuffer contents are allowed, and the identical custom-u16 getrandom error is wrapped as Os. The ghost provider token may advance on error. This does not quantify every valid OS/internal error representation, model internal partial-write history or establish a real OS-state refinement. Actual buffers, Result/From, moves and Drop remain; only OS fill is abstracted. No uniformity, independence, freshness, E1 law or caller transport follows.

Full-outcome Kani052 timed out240s;053 changed the retry-loop unwind to17 while retaining safety/unwinding checks and also timed out240s. Neither proves success, sixteen rejections, final error, returned seeds or full cleanup events. No limit was raised. Fresh Charon049 identifies exact factory and returned-owner drop sites with unchanged zeroize bodies. Syntactic drop-site inventory is source association, not runtime exactly-once/order or P6 event transport. Generic projected Drop/Option<&mut T> still blocks the current accepted translation route. The prior sequential zeroize component proofs and source-inspected lifetime argument retain their limits.

Lead independently checked81 integrity files,7 receipt rows, source inclusion/span matching, recorded caps/admissions and zero swap without replaying verification. Kani051 exit0,2.140s,272060KiB;054 exit0,18.001s,505956KiB;Charon049 exit0,0.981s,198192KiB. Exact commands/hashes/revisions are in factory-cleanup/ledger.json. Timeout parent GNU RSS undercounts killed grandchildren;053's sampled aggregate2122996KiB and cgroup peak2147975168 bytes are not exact RSS. charon-driver hashes remain explicitly postrun-only. Cargo lock normalization preserves the parsed dependency graph; the first denied audit remains retained. No Lean theorem or changed premise is claimed.

Cumulative backend15/16,extraction49/52,Lean236/260,Kani54/60. Worker34644 continues as FactoryIteration, at most4 of6 remaining Kani,3 remaining extractions,24 remaining Lean and2 optimized Rust checks. It must establish a real iteration invariant/source relation before finite16 composition; no unchanged timeout increase or generic wrapper substitutes. A proof-local source fission snapshot may be designed under D187/D191, with actual implementation correspondence still required; this step does not authorize crates/programs edits or adoption. Outer8, adaptive public policy, durable ledger, cleanup/error observables, E1/L1/L2/L3 and native/artifact/performance gates remain required. Both deployed targets remain not yet established.


## D206 — One-draw candidate relation checked; actual source factoring is the next deliverable (lead, 2026-10-24)

Reviewed unmerged prover candidate4b3e17fb01048bb79c26ff2363a5475827e58f1a, its full cut harness/body/interface, byte-factor map, report and read-only final audit. Kani056 proves the one_draw CANDIDATE for every entry0..15,nonce32,postbuffer64,Ok/Err choice,custom-u16 error and ghost provider token: exactly one freshzero64 draw, identical error wrapping, Some iff both halves nonzero with exact returned32 owners/nonce, otherwise retry advances exactly1, including entry15->16. Real Drop remains enabled. This is a different source item/signature from actual generate_for_mask_nonce. Byte factoring is checked; actual caller/MIR equivalence and finite16 composition remain unproved. Ghost bookkeeping does not refine OS hidden state or imply freshness, independence, uniformity or E1 law. Physical cleanup events/order/provenance/unwind/hardware remain open.

Kani055 actual loop invariant and057 explicit-frame variant both timed out240s; no proof or counterexample follows. This invariant method is stopped. Kani056 exit0,31.68903409698396s,1802592KiB GNU RSS;055/057 wall241.470718/241.461047s with incomplete parent RSS. Their sampled aggregate peaks6567208/6571376KiB and cgroup memory peaks6704115712/6708342784B are distinct metrics, not exact RSS. Swap0. Every scope recorded6G/8G/noSwap/Tasks64/full-hierarchy before/go admission; max projected32.375GiB. Exact commands/source/dependency/tool preflight+go pins/revisions are in factory-iteration/ledger.json. No Lean, extraction, backend or ELF gate ran. Lead independently reran only the inspected read-only final audit: annotation erasure, cut factoring, four receipt fingerprints/caps/admissions and no shipped-source diff passed before the next worker launched. No verification replay or new theorem premise is claimed.

Budgets now backend15/16,extraction49/52,Lean236/260,Kani57/60. FactorySource worker38745 continues the same candidate with at most2 of3 remaining Kani,3 remaining extractions and24 remaining Lean. Under existing D187/D191 authority, its explicitly expanded scope permits a narrow ACTUAL host fission in state_only_entropy.rs after committed design and extraction preflight. The goal is an actual called helper/controller association, rather than another duplicate proof-only cut. Preserve original public API, guards/errors/draw order/retry-before-drop order/moves and16/outer8 behavior; no new trust, backend adoption, protocol/verifier or E1 change. Source/native equivalence remains required, and unsupported extraction/Drop semantics must fail closed.

New per-step optimized Rust allowance: at most3 focused checks/tests plus3 all-three-ELF build/gate commands. Any crate edit requires all3 current ELF identities after final source; absence of a gate keeps the candidate unadopted. Factory>=1000 small differential cases, if run, cannot replace D187's whole-prover identical-coin proof bytes/1000 comparisons. Native/effect/refinement, actual selected client, E1/L1/L2/L3, quiet median<15s and<=10% slowdown remain adoption gates. No unchanged full-BMC retry, higher cap or generic Guard/backend campaign is authorized. Both deployed targets remain not yet established. Port18COHERENCE33570 remains live on its own previously pinned branch/budget.


## D207 — Prospective factoring retained; corrected smaller extraction admission and effect interface (lead, 2026-10-24)

Reviewed unmergeddc26b384f5, full factory-source report/relation/proposed controller/helper and reservation/scope/runner/audit code. Prospective text calls the056 helper with a changed private visibility, but production source remains unchanged. No helper/controller equivalence, finite16 theorem, native effect relation or extraction was established. Existing pure (nonce,retry)->Result interpretation cannot represent repeated equal-input calls with different OS outcomes.056 still covers custom-u16 normal output/retry only; it supplies neither universal Error nor whole-helper event/frame/provenance semantics. No new trust or hidden whole-owner premise was accepted.

All3 preflights050-052 denied BEFORE scope/compiler/extractor. Preserve3 charges and ZERO new actual invocations.050 double-counted hierarchical uncapped current;051 counted reclaimable build pagecache;052 corrected those extra-reserve errors and retained25065172992B resident reserve. Its mandatory finite reservations+requested8GiB were34762391552B<55GiB, but adding7GiB OS/control reserve exceeded host MemTotal by645095424B. This was an EXTRA reserve denial, not failure of the mandatory55GiB gate or proof focused extraction is impossible. Missing sysroot rlib preflight pins and untimed/unretained raw stderr remain explicit limits; no retroactive at-go gate exists.

Lead reran the inspected read-only audit before relaunch: exact prospective/original/056 source identities,3 rejected admission receipts/fingerprints, archived source hashes and no compiled artifacts passed. No proof replay. Then a fresh read-only corrected scanner diagnostic at2026-10-24T17:50:24.218260Z for2GiB request returned allowed=true: finite26172456960B,projected28319940608B,uncapped resident25021128704B,OS/control reserve7516192768B,MemTotal66698661888B,MemAvailable55812419584B. This diagnostic is not a future launch barrier. Prior focused factory Charon049 peak198192KiB supports a smaller preflight rather than another8GiB reservation.

FactoryState46554 continues the same branch. Explicitly authorize LOWER1536MiB/2GiB/noSwap/Tasks64 scopes ONLY for focused selected-item Charon/Aeneas preflights. Preserve both reservation/headroom gates, full hierarchy and fresh before/go, sysroot/library/tool pins and stderr/timing. Larger Rust/ELF jobs retain6G/8G limits and require their own allowed fresh gates. No service/cache/other-owner mutation, higher cap or historical resource repair. Read-only admission diagnostics should test scanner changes before compiler reservations; one correctly denied target should not trigger unchanged retries.

Lead adds4 extraction reservations:52/52charged ->ceiling56,4available; last3 were pre-extraction denials. Backend15/16,Lean236/260,Kani57/60 unchanged;max2Kani this step. Source-step optimized Rust checks/tests0/3 and ELF-gate commands0/3 carry forward, no new Rust allowance. Under existing D187/D191, resolve the known pure-helper obstruction with a sufficient actual owned-state/event interface before spending extraction on that interpretation. Preserve Err advancement outside Result and distinguish native operational state from OS-world/freshness; a reset cursor/ghost counter is insufficient. Weakest sufficient event/primitive-outcome transport is permitted only with proof of experiment transport, not mere output equality. Literal E1 successful64 contextual law stays explicit; no new freshness/independence/trust. Narrow selected host factory/owner call-site rewrites remain gated; no protocol/verifier change or source adoption. All3 ELF, whole-prover fixedcoin1000, native/effect/client/E1/L1/L2/L3 and timing gates remain. Both deployed targets not yet established.


## D208 — Owned request/resume preflight succeeds; concrete Drop/P6 contract next (lead, 2026-10-24)

Reviewed unmerged1097f5bef9 and complete FactoryState prospective native Request/Draw/Control/resume source, report, audit and precise blocker. The proposed real draw calls getrandom fill on freshzero64 and carries the actual buffer plus Ok/Err into deterministic resume, avoiding the earlier fixed-pure-helper interpretation. No production source edit, native/source refinement, finite16 theorem or privacy claim follows. Native operational control and abstract OS world remain distinct; the model's required Err advancement and outer8/durable ledger/E1/L1/L2/L3 transport are still unproved.

Optimized Charon054 actually passed atb2fdc3463b6ebabc24e1dcbef4644a750a9ea6ee: reported target0.85s,198956KiB,swap0; runner6.082497532s,aggregate238360KiB,cgroup memory peak226746368B. Fresh1536MiB/2GiB/noSwap/Tasks64 before/go admission and pins passed, including189 sysroot rlibs. Projected finite reservation28319940608B; resident before25061765120B/go25062354944B plus7GiB control reserve passed. LLBC size810227B,SHA432e627f6ea4705ced509cd70db4e9be65f2e0736c3a8d260e2895ea0ab2573a retained as hash/size only. No Aeneas invocation: actual glue15 normal Drop796 projects a generic inner field to a trait target, outside the exact pinned014 implementation's supported shapes. Seven unsupported Drop sites are preserved. This is a source/backend assessment, not a fresh failed Aeneas run or mathematical impossibility.

053 remains a charged missing-input guard failure before admission/compiler, with originals/stderr/timing retained. The earlier mixed-snapshot diagnostic error was corrected before the real admission; no policy weakening. An oversized6657819B pretty emission-audit JSON failed and is retained as hash/size; compact identical parsed data passed. Lead independently reran inspected integrity audit with exactly2 evidence writes suppressed: original/prospective source association, actual/guard invocation ledger,189rlib and before/go hashes, corrected scopes/reserves, static blocker and absence of compiled/oversized artifacts passed. No proof/runtime replay, changed premise or new trust.

Budgets now extraction54/56charged,2remaining; this step1guard+1actualCharon,0Aeneas. Backend15/16,Lean236/260,Kani57/60 remain. Rust checks/tests0/3,ELFcommands0/3 carry. ResumeP6 worker52487 now targets the concrete prospective resume/native-driver contract with every valid host NonZeroI32 getrandom error, exact live returned owners/control and real Drop events/order/frame. Reuse old zeroize proofs in their limited scopes; no Drop replacement, ghost-token-as-OS-world, source-erasure-by-assertion or generic Guard/backend campaign. If proof instrumentation is needed it must preserve actual destructor execution and justify erasure/noninterference/admissibility, lifetime/provenance limits explicit.

At most2 of3 remaining Kani; existing2 extraction/24Lean slots and old Rust/ELF allowances only, no new formal allocation. Focused extraction keeps2GiB. NEW resume/event Kani scope may use LOWER3GiB/4GiB/noSwap/Tasks64, justified by056's2259732KiB aggregate predecessor;2GiB is too small for this class. This is a new contract, not a higher-cap OOM retry. Full fresh reservation+resident+7GiB reserve remains mandatory, no higher cap after failure. Native/world source/effect association, original factory equivalence/finite16, outer8/adaptive public policy/ledger, E1/L1/L2/L3/client, all3 ELF/whole-prover differential and performance/adoption gates remain open. Both deployed targets not yet established.


## D209 — Concrete real-Drop packet reviewed; scalar source/erasure preparation before final slot (lead, 2026-10-24)

Reviewed unmerged ResumeP6 through7e900bb534, actual prospective Request/Draw/resume/controller source, all-error contract, real Drop observer hooks, source patch map and explicit erasure/owner limits. Lead independently reran inspected packet audit with1 output write suppressed: exact source spans, package identities, pre/go/post tools/sysroot/dependency hashes, corrected full hierarchy/resident gates and scopes, receipts/budgets passed. This is source/receipt consistency, not native proof. Production source unchanged and candidate unadopted.

Actual Kani058/059 both exit124 after240s target timeout, runner243.213565401/243.103223525s. Compilation0.96/0.98s then symbolic checking; no verification result/counterexample.059 materially removes scalar Snapshot construction but still retains full array event snapshots. Preserve both failed packages/receipts unchanged. Actual cgroup peaks3368935424/3385516032B under3GiBHigh/4GiBMax/noSwap/Tasks64;swap0. Raw sampled aggregate6288248/3319468KiB may double-count shared parent/fork pages; GNU time16168/15840KiB is incomplete for killed descendants, neither is relabelled exact native peak. No higher cap or timeout retry.

The safe cfg-kani constructor covers all valid NonZeroI32 host error representations, not an OS errno law. Observer reads current live destructor borrows and actual volatile/fence/Drop bodies remain; source reverse-patch identity is syntactic only. Equal event payloads/ordinal counters do not prove persistent field/leaf owner identity. Semantic erasure, native P6/frame/order, OS-world/error transport and actual controller reachability/finite16 remain unproved. No Lean theorem or premise/trust changed. E1/L1/L2/L3/outer8/adaptive public policy/ledger/full transcript and all adoption gates remain open.

Budgets Kani59/60 (2 new attempts),Lean236/260,extraction54/56,backend15/16; Rust0/3 and ELF0/3 carry. ResumeScalar61137 continues same candidate at7e900bb534 with ZERO Kani (last slot RESERVED), at most8 of24 remaining Lean, at most1 of3 existing focused Rust checks, no new extraction allowance or backend build. Implement universally quantified one-coordinate scalar observer, with two corresponding positions for64, actual source-role/move association and sufficient ghost totality/disjointness/semantic-erasure argument before requesting the final proof run. Full-array observations cannot be called scalarized merely because downstream assertions select one byte. No Drop stubs, unsafe lifetime shortcuts or token-as-OS-world. New source-specific proof preparation must retain all inputs/errors/control and exact real Drop execution. Both deployed targets remain not yet established; no new production edit/adoption.


## D210 — Scalar observer reviewed; concrete success-role/MIR producer next (lead, 2026-10-24)

Reviewed unmerged8bd72836ff complete ResumeScalar source/RELATION/FINAL-SLOT/paired harness/observer/metadata/finiteLean/compile/audit. Lead independently reran inspected packet audit with1write suppressed. One entryselected j covers all32coordinates and both64halves; event payload384->12bytes, no observationloops, structural reductiononly (pair executes source twice; no wholesolver-costclaim). ActualDrop/iterator/scalarvolatile/fence remain, complete arbitrarynonce32/postbuffer64/entry0..15/validNonZeroI32errors preserved. Ghostrecord literalbranches/sentinel/overflow avoid sourcepathpanics; disjoint-store/typed-borrow stuttering remains inspected argument, not native semantic erasure. Source-place roles distinguish equal-valued owners, but successmove/returneddisposal lacks freshcompiled witness. Old054rejectiondrops/retryorder reused; empty recorded successIf branch does not imply actualsuccessimpossible. No native/P6/world/controller closure or premise/trustchange.

FouractualLean compiles236->240/260:coordinate239exit0,capacity240failedomega(defaultdidnotunfold),changed241exit0,audit242exit0; eightstandard-or-emptyaxiomreports,swap0,RSS<0.7GiB. Failed240sorryAx diagnostic rejected and originalpreserved; reconstructedreceipt transparentlylacksrunnerwall. Twoearlierimport-pinguards were preLean (noc newcompilerinvocation). Focusedpacket auditexit0,1.21s,102219776B,swap0. Rust001exit78 admissiondenied beforecompiler; finite+requested8GiB34762391552B<55GiB but uncappedresident31026192384B+7GiBcontrolfailedphysicalreserve. Nogo/compiler/typecheck; no unchangedretry/capraise. Olddeniedsnapshot isnotfinalsourceidentity; exactassessment/hashonlyoversizedJSONretained.

BudgetKani59/60unchangedlast1RESERVED; Lean240/260;extraction54/56;backend15/16;Rust1/3conservativecharge from1deniedadmission,actualcompiler0;ELF0/3. ResumeRoles66304 continuesat8bd72836ff withZERO Kani,atmost6of20remainingLean,atmost1NEWordinaryRust/MIRinvocation(2ndof3charges),atmost1of2remainingextractiononlydemonstratedsupportedconsumer,backend0. Must obtain concrete normalpathdraw/resume/success aggregate move/dropflag/returneddisposal source association and sufficient scalar instrumentation projection underexistingapprovedtool semantics. Don't demand generalizedRust/LLVM/hardwarecertification as inventedprerequisite; don'tclaimMIR/sourceargumentnativeproof orhidewholehelperresult. FinalpairedKani remains reserved forleadreview.

Explicitlyauthorize LOWER1536MiB/2GiB/noSwap/Tasks64 for this tiny ordinaryRust/MIRcompile class, justified bysamefamily optimizedcompile0.96/0.98s andfocused054RSS~200MiB. Prior8GiB denial launchednothing; lowerrequest isn'tpostOOMincrease. Readonly2GiBdiagnostic BEFORE spendingreservation; retainstrictfinite<55GiB andcorrectedresident+7GiBreservebefore/go. No services/cache/otherowner/A/key/RPC/chain changes. Ordinary cfgprover_rw_resume_scalar compile doesn't typecheck cfgkani checks; nohiddenKani budgetdodge. No productionchange/adoption; E1/nativeworld/errortransport/finite16/outer8adaptivepolicy/ledger/fulltranscript/L1L2L3/client/all3ELF/wholeprover1000/quietmedian<15s/<=10%slowdownremain. Bothsecuritytargetsnotyetestablished.


## D211 — Success moves recovered; admitted smaller ordinary MIR scope (lead, 2026-10-24)

Reviewed unmerged ResumeRoles f033f68bf7, the complete report, relation, inspection/audit and corrected actual structured control. Lead independently reran its read-only packet audit:15 source/dependency inputs matched, no new compiler/proof invocation. Old054's empty inner true arm455 falls through the enclosing suffix:467/469 move field10/leaf12 into named destinations;470 builds Secrets,474/476 wrap Some/Ok,478 assigns return0,607 drops bytes64,613 returns. The rejected arms terminate before that suffix. Both32 fields stay live in the returned aggregate during bytes64 cleanup. Exact source places, return/error constructor, rejection retry-before-drop order and owner field1-before-field2 glue are retained. This corrects only the prior missing-success-witness assessment; historical packets are untouched. It is inspected association from reused emission, not fresh native projection, raw MIR flags, current hook/draw/run proof or OS-world transport.

The worker's read-only2GiB diagnostic denied: projected finite28319940608B + exclusive uncapped resident31727083520B +7GiB control7516192768B =67563216896B > MemTotal66698661888B. No reservation/compiler/retry or budget charge followed. Focused packet audit exit0,1.07s,RSS102121472B,swap0,axioms N/A. Budgets remain Lean240/260,Kani59/60 final1 reserved,Rust1/3 conservative prior charge/actual compilers0,extraction54/56,backend15/16,ELF0/3.

Lead then ran a distinct read-only1GiB diagnostic after verifying exact reservation script hashes against the job's remote copies. It passed: projected finite27246198784B + uncapped resident31733690368B +7GiB control7516192768B =66496081920B <66698661888B; MemAvailable55777615872B. Full162660-byte diagnostic retained in scratchpad/manager-resume-1g-diagnostic-20261024.json. This is source/resource evidence only, not a future launch barrier or compiler receipt.

ResumeMIR70362 continues atf033f68bf7. Explicitly authorize LOWER ordinary compile scope High768MiB/Max1GiB/Swap0/Tasks64 and one cargo compiler job for the tiny current scalar package, supported by prior family optimized compilation0.96/0.98s and focused054 RSS~200MiB. Neither larger denied predecessor launched a compiler or OOMed. No Kani cap or timeout is raised. Preserve all full-hierarchy/resident/7GiB-control gates with fresh before/go and exact1GiB scope. At most1 NEW ordinary optimized Rust/MIR attempt from the existing allowance; no new extraction/backend/Kani/ELF, final Kani slot remains reserved. At most4 of20 remaining Lean only for a concrete producer, not unrelated wrappers. Need current draw/resume/run/hook source places, built/drop-elaboration MIR and exact flags/loans where retained, then a justified concrete projection. Ordinary cfgprover_rw_resume_scalar excludes cfgkani checks; no hidden Kani frontend invocation. Native/world/error/controller/E1/L1/L2/L3/client/adoption obligations remain. Both deployed targets not yet established.


## D212 — Current scalar MIR association audited; paired native check still reserved (lead, 2026-10-24)

Reviewed unmerged dcc848acfc complete ResumeMIR report, relation, 59-line concrete MIR inspector and audit. Independently reran the read-only packet audit:170 inputs, all132 retained built/NLL/drop-elaborated/optimized MIR texts, current source/package/dependency summaries, recorded pre/go/post equality, exact scope and resource snapshots passed. No compiler or proof replay by lead. The current draw freshzero64/literal fill/borrow end/named moves, resume success/error/rejection cleanup, run phase before owner disposal and actual57/58 drop flags, active Drop pre/shared -> mutable Zeroize -> post/shared loans and separate record statics are now associated by current compiler evidence. No identity is inferred from equal bytes or event ordinal. Full unwind paths remain, with no paired unwind theorem.

One ordinary optimized cargo rustc command passed in the explicitly lower768MiB/1GiB/noSwap/Tasks64 scope, jobs1/codegenunits1: build5.72s, wrapper9.698120232s,processRSS210192KiB,aggregate283284KiB,cgroup805830656B,swap0. All50077 pre/go/post source/tool/sysroot/dependency file pins matched; full fingerprint63746246066065c3885fbdb48de006d5bf5dec11c7c9d6fe8a70c541327d7ded. Exact source-stage revision ac5614d248 and input hashes qualify what compiled. cfgprover_rw_resume_scalar excludes cfgkani and its error constructor/checks: no harness typecheck, execution or native relation is claimed.143929 dump-file inventory is retained remotely by hash/size; no binary/object commits. Complete current MIR closes the inspection obligation, not native P6/OS-world or whole privacy.

Existing BuilderDropObservation.P6Route still assumes sourceDrop=dropSpec for every modeled memory; it has no current typed-hook producer. Heap-frame lemmas and generic NativeDrop/Erasure callbacks do not replace that missing source instance. Current source loans/static-store stuttering is an inspected argument pending concrete paired validation. No native equality premise, new trust/freshness/error-law assumption, or unrelated Lean wrapper was introduced. Last paired Kani slot remains reserved pending reviewed admission and exact final source/tool pins. NativeOSWorld/error transport, contextual E1, controller/rank/finite16/outer8/adaptive public policy/durable ledger/full transcript/L1L2L3/client and adoption gates remain open.

Budgets Rust2/3 conservative charges, actual ordinary builds1; Lean240/260,Kani59/60final1reserved,extraction54/56,backend15/16,ELF0/3. Source candidate remains unmerged/unadopted. Both deployed security targets not yet established.


## D213 — Final native slot reserved; complete resource denial retained (lead, 2026-10-24)

ResourceGO/THREADS audited and merged25b0b9df48 as UNADOPTED management evidence. All57 synthetic tests and full observed threaded/root/empty-group coverage are retained; the actual outside uncapped SSH scope denies GO. Lead independently replayed all ordered raw inputs/decisions with historical writes suppressed (exit0,0.354557541s,65,667,072B,swap0). Latest AFTER service stat components exceed exclusive current by4,096B; every prospective1/2/3/4/6/7/8GiB denies and current headroom is UNKNOWN. No consumer or build launched, no resource estimate adopted. Historical extra-reserve coverage omissions are explicit; no previous proof/source receipt is retroactively certified.

ResourceSTAT87430 studies exact Linux6.8 counter semantics and, only if justified, a full-charge/no-credit conservative candidate, preserving raw discrepancy and all other gates. It has zero build/proof/consumer/scopes and at most one changed-source read-only capture. SBFRECAPTUREPREP86302 prepares official archive/frozen-source/released-cache identity checks with zero builds. Current toolchain provenance merged009b61e61b is not historical pre/go identity or native memory/effect semantics. No cryptographic/native premise was discharged by these management jobs.

No new privacy proof/compiler validation. Last paired Kani slot remains reserved pending reviewed fresh admission and exact consumer pins. Budgets unchanged: Lean240/260,Kani59/60,Rust2/3charges(actual ordinary builds1),extraction54/56,backend15/16,ELF0/3. Current scalar MIR inspection and unmerged candidate limits remain D212. E1/native OS-world/error transport/controller/adaptive-policy/full observable transcript/L1/L2/L3/client/all-three-ELF/whole-prover equivalence and timing gates remain open. Both deployed targets not yet established.


## D214 — Conservative resource candidate reviewed; metadata-only live rehearsal (lead, 2026-10-24)

Reviewed ResourceSTATb9af8cde58, merged74d67bcc99 and removed clean owned worktree/branch. Full independent offline replay14,587 ordered events passed1.423225250s,79,282,176B,swap0,with historical writes suppressed, baseline source identity/tested source hashes checked. Former stat sum<=current assumption is unsupported across separate Linux reads/type versus LRU counters. Candidate fully reserves a qualifying uncovered discrepancy cell and zeros both cache credits across the pair, retaining all raw data/other errors. No new native/crypto trust or security premise. Old failed measurements remain denials; old4GiB candidate extra margin129690944B is historical only, current headroom unknown.

ResourceACTUAL91101 is LIMITED authority for one metadata-only prospective4GiB check and, only if it passes, one fresh actual High3G/Max4G/Swap0/Tasks64 scope with proc-derived GO additional0/count-once and a tiny post-GO marker. No compiler/solver/proof workload, broader gate adoption, cap increase or unchanged retry. Live controls/source/input receipts and full offline audit required. Passing this rehearsal would still not authorize final native verification; that needs separately reviewed consumer and fresh before/go. Kani59/60 final1 remains RESERVED; all other privacy budgets unchanged. SBF preparation remains zero-build. Both targets not yet established.


## D215 — Prospective rehearsal denied; no native slot consumed (lead, 2026-10-24)

ResourceACTUALb8275108bf reviewed and merged5756082d85. Independent full ordered15,015-event replay and exact raw report/input reconstruction passed without writes/network. Single prospective4GiB capture DENIED78 because derived system.slice exclusive anon was -14086144B (raw parent/children counters were individually unsigned). Current exclusive1085534208B stayed nonnegative. The unchanged gate rejected it; after-snapshot positive anon does not repair failure. NOscope,GO,marker,solver/compiler/proof/ELF or other workload ran. Host1.412283888s,82784256B,RSS,swap0;13 offline tests, pre/post source/runtime/env pins and all old failures retained. No counters/criteria silently changed or retry.

ResourceHierarchy96923 is limited to primary-source/offline full-cell/no-credit/debt-padding assessment on reused inputs; no new host read, scope or consumer. Live headroomUNKNOWN. SbfCachePrep94997 continues zero-build metadata/cache/provenance preparation after rehearsal termination. No broader resource gate or final Kani launch authorized. Private budgets remain Lean240/260,Kani59/60final1RESERVED,Rust2/3charges(actual ordinary builds1),extraction54/56,backend15/16,ELF0/3. Native/world/E1/L1/L2/L3/full privacy/refinement/adoption gates unchanged. Both targets not yet established.


## D216 — Global availability candidate reviewed; source provenance preparation (lead, 2026-10-24)

ResourceHierarchy04cd03a907 and SbfCachePreped3227f4da reviewed/merged/cleaned. Full-cell debt policy remains counterfactually denied;123 registry archive checksums/published contents match, two global source dirs have extra ICE-log filenames (contents never read/copied/deleted). Private cache export is retained reference, not historical compiler/source provenance. Cargo directly execs cached build scripts, so a compiler wrapper is not an all-descendant cold guard.
ResourceAvailablefbe04424e7 merged OFFLINE ONLY after independent full code/primary reserve argument and16groups/15,015-event exact original hash/DENY replay/6,908reads per new observer snapshot. Lead1.066378250s/174,718,976B/swap0. Explicit operator policy uses global MemAvailable minus ALL active file, KReclaimable-floor(SReclaimable/2), FULL root residual; full finite caps plus7GiB reserve and strict55/2GiB checks. Derived unused signed stat correlations diagnostic only, raw/missing/visibility/controller/PID/scope errors deny. Reused4GiB margin1,968,877,568B is historical only. Current headroomUNKNOWN/live API DISABLED/no native consumer. No security/native trust discharged or added.
SbfInputs7112 preparation-only zero builds scopes; prospective coherent initial~123crate cold dependency capture with sealed private archive-derived inputs replaces manager's warm-only plan, actual build separately gated and NOT authorized. No frozen/source/protocol/ELF change. Final Kani1 remainsRESERVED59/60; Lean240/260,Rust2/3charges(actualordinarybuild1),extraction54/56,backend15/16,ELF0/3 unchanged. E1/world/error/native/drop/controller/full transcript/L1/L2/L3/client/adoption/threeELF/equivalence/timing obligations remain. Both deployed targets not yet established.

D216 continuation: ResourceAdmit11116 limited metadata rehearsal authorized after independent review; ONEprospective4GiB, onlyifpassoneactual3G/4G/Swap0/Tasks64 GO+marker, no compiler/nativeconsumer. HostwaitsSbfInputs7112terminal. Unchanged59/60Kani final1RESERVED; no generalAvailableAPI adoption.


## D217 — Prospective admission passes; actual GO blocked before native work (lead, 2026-10-25)

ResourceAdmit5e59131ea1 prospective4GiB passed with421,640,192B margin; systemd scope child failed exactenvpin verification BEFOREactualGO/controlreads/marker. Differing fieldunknown, no security/Mac diagnosis. No native/compiler/solver slot used. All original artifacts/first liveattempt remain; fullbranchreviewpending. ResourceAdmit-v216979authorizedONEchanged-source metadatarehearsal using exactenv-i insideunit beforepinnedPython, strictpinpolicy retained, newstage/unit/sentinel/epoch andfreshfixed4GiB pre/GO. No unchangedretry,size search,capraise,generalresourceadoption or nativeconsumer.

SbfInputs independently308auditchecksPASS0.323102917s/37126144B/swap0, merged8373ebf51b andcleaned. Newprivate123package archives/source/index prepared; usernamespaceuid_mapEPERM/nochild retained. SbfClosure18006concreteinput/runtime/helper/trace prepONLY, waits16979terminal beforehostreads; zeroCargocompiler/scope/rootsetup. Future build-script arithmetic626480inversecalls mustbeoptimized; explicitbuildoverrideproposal withgeneratedtablesandall3fixedELFidentitygates, nosource/pin/protocolchange. No new crypto/native/trust premises discharged oradded. Privatebudgets Lean240/260,Kani59/60final1RESERVED,Rust2/3charges(actualordinarybuild1),extraction54/56,backend15/16,ELF0/3unchanged. E1/world/errors/native/drop/controller/transcript/L1/L2/L3/client/allELF/equivalence/timing/release remainOPEN. Both deployed targetsnotyetestablished.

D217 review continuation: full immutable initial ResourceAdmit source read and independent14,866-event/hash replay PASS0.613672625s/172998656B/swap0. Scope remains prospective-only; no GO/control/marker or native evidence. V2 separatelyallocated, Kani59/60reserved.


## D218 — Thread-drift denial retained; no native slot consumed (lead, 2026-10-25)

ResourceAdmitv2160e8876b6 reviewed/merged09cf0841c3/cleaned. Independent14926-event/fullhash replay PASS0.798621541s/169574400B/swap0; prior evidenceunchanged. New innerenv-i sourceconstruction pinned/strict, but freshprospectiveDENY unrelated serviceTID3871412exitbetween snapshots. No scope/GO/control/marker/nativeconsumer/compiler/solver. Bothliveepochs2/2used; no retry authorized. ResourceStability20214OFFLINEonly assesses crosssnapshot membership dependency in numericalcap/reserve policy; within-snapshot visibility/raw/control/error gates retain. Anychangedpolicy mustexplicitlypreserveoldDENY andprovenance, counterfactualonly,noadoption. Privatebudgetsunchanged Kani59/60final1RESERVED,Lean240/260,Rust2/3charges,extraction54/56,backend15/16,ELF0/3. SbfClosure18006prep nowcancontinueownhostreads afterv2terminal, stillzerobuild/rootsetup. Bothdeployedtargetsnotyetestablished.


## D219 — Reviewed structural policy, limited changed metadata rehearsal queued (lead, 2026-10-25)

ResourceStabilityfullcode/policyreviewandindependent3.637901375s/173785088B/swap0audit+8focusedgroupsPASS, mergedf7b90c8230/cleaned. All14926oldevents/hash/DENYpreserved. Unrelatedcrosssnapshotmembership equalityremovedONLYwhereitdoesnotenternumericfullcap/reserveformula; everyinternalsnapshotraw/visibility/PID/current/controllercheckretains, fullstructure/control/collectoridentitystable, prospectiveselfpresenceadded. Same55/7/2GiBstrictpredicates. Newcounterfactual209602560Bmarginisnotcurrentauthorityorphysicalfutureguarantee. PublicAPIdisabled.
ResourceStableGO25321LIMITEDONEchangedpolicyfresh4GiBprospective, onlyifpassoneactual3G/4G/Swap0/Tasks64GO+marker; strictsource/env-i/runtime/actualidentity/controls/pressurepins. HostwaitSbfClosure18006terminal. Prior2epochsremainfailed/charged. No nativeconsumer/solver/compiler/Kani launch. LastKani59/60RESERVED; allprivatebudgetsandnative/world/E1/error/drop/controller/L1/L2/L3/client/equivalence/timing/artifact/security obligations unchanged. Bothdeployedtargetsnotyetestablished.


D219 continuation: ResourceStableGO0c1e9aea87terminal/unmerged pendingfullreview; soleepochprospectiveDENY Docker runtimepage-summaryvirtualreservation error with newlyinherited512MiBRLIMIT_AS. Source line22 confirmslimitinrunner; exclusivecausalityunproved, physicalOOMnotobserved. No scope/GO/control/marker/native/Kani/ELF activity. No automaticretry; appropriateRSSguardreviewneeded, MemoryMaxunchanged. Kani59/60finalreserved andallprivatebudgetsunchanged; targetsnotyetestablished.


## D220 — Bounded preparation reviewed; native consumers remain unlaunched (lead, 2026-10-25)

ResourceStableGO0c1 reviewed/independent14,814-event exact hash/DENY replay PASS0.695641959s/163,037,184B/swap0, merged4f4b0a2470/cleaned. Address-limit virtual reservation denial retained, no resident OOM or exclusive causal claim. ResourceRssGO29365 ONE changed-source epoch authorized with sampled processRSS512MiB instead of AS lowering; terminal8478f742e8 failed unstaged bootstrap before prospective/GO. Locally repaired only, review pending, epoch charged/no retry. No native/Kani/compiler slot used.

SbfClosure full review+independent118 checks/39synthetic PASS0.101407125s/28,327,936B/swap0; merged65c4082110/cleaned. Partial manifests and disabled namespace draft are preparation only; real path anchoring/freshGO/runtime/trace/cache closure open. Future optimized build-script environment proposal opt3 planning-approved, all3 fixedELF/generatedtable identity gates retain, actual build unapproved. SbfResolve31012 atmost2 metadata CLI calls, guarded source-justified rustc queries/no codegen, private cache/config plus bounded exact public locked archives. Waits resource rehearsal terminal before host reads; metadata exception waives no future namespace/admission/trace/artifact gate. Both deployed targets not yet established. Private budgets Lean240/260,Kani59/60final1RESERVED,Rust2/3charges(actualordinarybuild1),extraction54/56,backend15/16,ELF0/3 unchanged. E1/world/error/drop/controller/full transcript/L1/L2/L3/client/equivalence/timing/adoption/release obligations remain open.


D220 review continuation: ResourceRssGO8478f742e8 fullsource/policy/guard/repair reviewed, merged/cleaned. Independent9groupsPASS0.289959625s/35962880B/swap0, localunstagedbootstrapregressionPASS0.155170667s/samechildmaximum/swap0, causalreplayPASS/nohost. Leadwrapper allfieldscomparisonfailedonlyaudit-source_revisiond1edd297ea→8478f742e8; exactdifference/ancestry/allotherfieldsconfirmedfromretainedrebuiltartifact, no rerun/nohistoricalrewrite. Fourmetadataepochsfailed/charged, no runtime/prospective/GO/nativeconsumer; repairedsourcehostvalidationOPEN/no newepochyet. Kani59/60finalreserved, privatebudgets/targetsunchanged. AselectedSDK/S1rawdelta andbinder-sensitiveownerdataauditindependentlyverified; enclosingPort30joinpreparationzero-compilers/host. No privacy/native/world/E1/L1/L2/L3 orreleaseobligationdischarged.


D220 allocation continuation: ResourceRssGOv234318 newownworktree/branch entryf29c3e0e8c, ONEfreshmetadataepoch on reviewedrepairedbootstrap only, zeronative/compiler/Kani/root/scopesexceptexplicitmetadata3G/4GGOifprospectivePASS. AllFOURpreviousmetadataepochsremainfailed/charged, noreset. Localcriteriaprep/sealednormalizedidentitydiff/newunstagedbootstrapregressionfirst; nosemanticredesign. MUSTwaitSbfResolve31012terminalbeforeANYhostactivity. Ifstillliveafterindependentprep+one60swait, commitWAITINGwithallocationunused. Samefullpolicy55/7/2GiB/source/env-i/inheritedlimits/sampledprocessRSS/actualscopecontrols andfailclosederrors; freshstage/unit/epoch, no liveAPI/consumeradoption. FinalKani59/60reserved andallproofbudgetsunchanged. Port30JOIN32946localzero-compilerconcretejoinpreparationcontinues. Bothsecuritytargetsnotyetestablished.


## D221 — Frozen metadata resolved; portable resource boundary reviewed (lead, 2026-10-25)

SbfResolve21341c8589 fullsource/primaryCargo/receiptreview andindependent8362checkauditPASS0.147692542s/46088192B/swap0,34guard+9fixturecasesPASS; sets/censusbyteidentical. Merged50ab99cfbf/cleaned. Actual2metadataqueriesREUSED:357graph/344registry,3print-onlyRustc/no crate/buildscript/procmacrocodegen,0.543161591s/132997120Bsampledaggregate/swap0.428privatecachepackages/394indicesconservativesuperset,371opened, no downloads. Notselectedcompiledunits/privateimmutable/runtime/trace/cache/native/ELF/securityclosure. Futureopt3build-scriptproposalretainsall3ELF/generatedtablebytegates; nobuildpermission.

Resourcev2468bootstrapSSHsucceededbutMaclocalcheckmisreadLinuxunlimited-1; no stage/prospective/GO. Exactcausereview+independent12mapping/3groups0.702223375s andcausalaudit0.436115833s/37650432B/swap0. MinimalPORTABILITYabcdindependent6groupsPASS0.533885833s/37404672B/swap0,11/12modulesunchanged/fullnumericmap/env/control/guardpolicyretained; mergedb8fcc2dad5/cleaned. NewfixedLinux/-1wirevalidation distinguisheslocalDarwinconstantswithoutlimitsetters/newtrust. Fiveoldmetadataepochsremainfailed/charged. Resourcev340856ONEnewmetadataepoch6 onreviewedcode,4GiBpreonlyifpass3G/4G/Swap0/Tasks64GO+marker, no consumer/Kani/root/compiler. Bothdeployedtargetsnotyetestablished.

SbfSeal37015SOURCEONLYhardensdisabledrootsetup/sourcepathanchors/FD/stdout/GOroute, host/root/ns/compiler0. Port30concreteSDK/S2/S1joincandidate reviewed/merged66dec5b4d8, uncompiled/noclosure. Leadrecoveredtwohash-pinnedclosedS8objects; Port31atmost2localattempts fromsoundnessunassigned352→<=354, no privatebudgetspend. PrivateLean240/260,Kani59/60finalreserved,Rust2/3charges(actualordinarybuild1),extraction54/56,backend15/16,ELF0/3unchanged. Fullnativeworld/E1/error/drop/controller/transcript/L1/L2/L3/client/equivalence/timing/adoption/artifact/release obligationsretain.


## D222 — Existing GO denial explained; concrete setup remains disabled (lead, 2026-10-25)

SbfSeal b6ac source fully reviewed/independent32 cases and895 checks passed, merged9f48e742a9/cleaned. Descriptor-anchored exclusive inputs, sealing and bounded parent output descriptors are concrete preparation only; actual Linux namespace/mount/pidfd/backend still disabled. SbfLinux44932 source-only/mocked tests, host/root/compiler0. No native, P7 memory/effect, runtime/trace/artifact closure follows.

Resourcev3 allocation6 inspect/stage/preflight passed, run78 stopped/charged. Separate ONE existing-capture read exported28 of29 finite entries, marker explicitly absent; no new admission. Capture45d137dd34 independently replayed all29595 ordered events/full byte-identical reports/maps/control/exit receipts in5.183699542s/277741568B/swap0; merged7f6719926f/cleaned, original2512 transport fragments retained externally. Prospective4GiB margin94404608B passed; actual3G/4G GO denied552960B reserve shortfall, controls passed, cgroup peak105644032B/swap0/pressure0. This explains exit78 without a supported Mac hardening/crash/OOM claim. All six failures remain charged. Failed Darwin/Linux errno offline harness and corrected exact-error replay retained; first replay metrics UNKNOWN. No solver/compiler/native slot consumed.

ResourceMeta1G48717 SOURCE ONLY prepares tighter768M/1G metadata scope and matching prospective1GiB/actualQ0 controls, exact full55/7/2GiB policy unchanged. No fresh host epoch allocated;1GiB metadata never authorizes4GiB Kani or6G/8G build. Final Kani59/60 remains reserved. Port31 separate soundness353 new Bool no-axioms fact/354 failed data export, corrected one355 data-only allocation; no privacy budget used. Private Lean240/260,Rust2/3charges(actual ordinary builds1),extraction54/56,backend15/16,ELF0/3 unchanged. E1/world/error/drop/controller/Claims/Terminal/transcript/L1/L2/L3/client/equivalence/timing/all3ELF/adoption/release obligations open; both deployed targets not yet established.


## D223 — Concrete Linux source reviewed; tighter metadata rehearsal allocated (lead, 2026-10-25)

SbfLinux9f50 complete typed ABI/backend/source/mock/failure review and independent54 final-source cases PASS0.096289833s/34209792B/swap0 plus source/package audit PASS0.054179708s/25575424B/swap0; package/command bytes identical. Mergede8100b8d12/cleaned. NEW mount-root fd, finite tmpfs/private PID1 proc, CPython gated fork/pidfd ownership, fd closure/drop and bounded parent outputs are concrete unexecuted source. Runtime/producer null, privileged entrypoints disabled; no actual host/root/probe/native/compiler/security closure. Raw-clone/prototype/capture-join failures retained. Actual LSM cancellation/D-state/parent-death/runtime gates remain.

ResourceMeta1G13ab full delta/source/manifests reviewed, independent six-module reversed bytes/fullAST plus8 focused groups PASS0.595988625s/37191680B/swap0; merged19bd47bc72/cleaned. Own clone adapter import failed before suite, retained then corrected without source change; failed metrics UNKNOWN. Tighter metadata768M/1G, Q1GiB versus actualQ0, all policy55/7/2GiB/limits/env/pins/other reservations unchanged. LIVE51248 ONE explicit new global epoch7, all six failures charged/retained. Metadata marker only; no larger-consumer/Kani/build authority. One finite existing-capture export after run is allowed even if run fails; no retry/new scan. Final Kani59/60 remains reserved.

Port31 separate soundness355 strict readbacks/43guards reviewed/mergedda9602be04; Port32 actual enclosing consumer MAX2 local356/357 allocated, no privacy budget borrowed. Private Lean240/260,Rust2/3charges(actual ordinary build1),extraction54/56,backend15/16,ELF0/3 unchanged. Nativeworld/E1/errors/drop/controller/Claims/Terminal/full transcript/L1/L2/L3/client/equivalence/timing/artifact/adoption/release obligations open. Both deployed targets not yet established; no new trust or contract change.


## D224 — Metadata GO reviewed; native permission remains separate (lead, 2026-10-25)

ResourceMeta1G c7bbb LIVE actual GO_MARKER_PASS independently replayed29639 ordered events/full report bytes/pins/limits/actual marker/control/identity/frontier in6.904315375s/274186240B/swap0, reviewed/mergedae091370b6/cleaned.29/29 capture entries/61019841B/20frames and2511 retained transport fragments verified. Seven operational/test files exact13ab; six helper identity-only copies exact45d/fullAST. New-data harness success/Q1 assertions explicit, evaluator unchanged; local summary-packaging error retained/corrected without replay or host retry. Actual768M/1G/Swap0/Tasks64 controls,cgroup peak105762816B/zero pressure/swap,inside3063519232B margin. Timestamped metadata only, no larger-consumer/current-headroom/native authorization; six prior failures charged. No supported Mac port-hardening cause for explicit reserve denial.

SbfRuntime54132 MAXONE bounded guarded public runtime-data acquisition sequence, no root/sudo/ns/mount/backend/syscall/guest probe/compiler/solver/ELF build, no use of old marker. Must retain exact finite Python/loader/stdlib/extension/cache metadata and uncertain conditional/pyc/runtime bindings; no full runtime proof inferred from modules/maps. Actual producer/finite probe/LSM/cancellation/parent-death/native/artifact gates open. Port32 local actual enclosing kernel consumer continues independently. Private Kani59/60 finalreserved,Lean240/260,Rust2/3charges(actual ordinary build1),extraction54/56,backend15/16,ELF0/3 unchanged. E1/world/errors/drop/controller/Claims/Terminal/full transcript/L1/L2/L3/client/equivalence/timing/adoption/release remain; both deployed targets not yet established.


## D225 — Partial runtime data reviewed; native loader trace and producer source allocated (lead, 2026-10-25)

SbfRuntime087f partial85files22203242B/12ELF70module30pyc reviewed/independent205checks0.538991792s/30752768B/swap0, merged338af425c9/cleaned. Old one SSH terminal78 on immediate-prefix/usr/lib64 PT_INTERP chain, remainder unobserved, not runtime incompatibility; partial86mapping30224170B candidate unapproved. Original3.9 local receipt failure remains1/unknownmetrics; independent3.12 same source audit passes and coverage/candidate outputs byte-identical. No host retry, changed rlimits, privileged/native/compiler operation or security obligation discharged.

RuntimeTrace58497 ONE bounded guarded public metadata sequence/onefixed unprivileged strace→Python import/data observation, explicit bounded intermediate alias/final-owner checks/native opened-unmapped/FD/negative/error coverage; no guest/root/ns/backend/compiler. Producer59431 SOURCE ONLY concrete future3G/4G recomputation/collector-sudo-monitor-helper binding and disabled fixed package/deployment artifacts; all host/root/fork/exec/probe/compiler0, no old1Gmarker/projection accepted, no user approval sought before concrete artifacts/runtime gate review. General APIs and actual privileged entries remain disabled.

Port32 separate soundness356/357 failed before reconstruction, original application/composed target unvalidated; two preceding source Bool shims no axioms. Material358 one consumer slot pending; no privacy budget borrowed. Private Lean240/260,Kani59/60final1RESERVED,Rust2/3charges(actualordinarybuild1),extraction54/56,backend15/16,ELF0/3 unchanged. Whole E1/world/errors/drop/controller/Claims/Terminal/transcript/L1/L2/L3/client/equivalence/timing/artifact/adoption/final replay obligations retain. Both deployed targets not yet established; security contract/frozen artifact pins unchanged.


D225 continuation: Port32 material358 reviewed/mergedb1742a83cc as candidate+FAILURE evidence, not closure; actual6060 strict core matches then Query31 stronger-dependency mismatch and13 private-name metadata collision pairs. Port33 focused359 fromlastunassigned, BOTH remainingwholeconsumer slots untouched, no privacy budget. RuntimeTrace2ce and Producer20a terminal cleanUNMERGED fullreviewpending: collectorSSL-alias78 despite tracee0/complete loader chain reported, source producer/deploy artifacts UNREADY/runtime pins missing, no actualroot/ns/probe/compiler. No new privacy/native/security claim. Both deployed targets remain not yet established.


## D226 — Focused Query31 failure retained, privacy budgets unchanged (lead, 2026-10-25)

Port33 actual359 parsing failed before raw reads/kernel checks; independently reviewed/merged as failure evidence, not closure. Port34 ONE raw-only local360 from soundness carry, no host/private budget use, no unchanged enclosing replay. Both reserved consumer calls preserved; all SDK/std/runtime/allocator/extraction/native/artifact boundaries remain. RuntimeTrace2ce/Producer20a still terminal/unmerged/full-review pending. Private Lean240/260,Kani59/60final1RESERVED,Rust2/3charges(actualordinarybuild1),extraction54/56,backend15/16,ELF0/3 unchanged. Both targets not yet established.


D226 continuation: RuntimeTrace2ce reviewed/independent76+9+116checks with sixbyteidenticalderivedoutputs, merged0ba402c016/cleaned; actualtracee0/collectorSSLalias78 remainspartial/unapproved. Producer20a reviewed/independent15finalmocktests/7copies/17installrows/exactdelta, merged5a02c982e7/cleaned; NOTHING INSTALLED/entriesdisabled/runtimeabsent/activationunapplied. New SbfRuntimeFinish source-only finiteSSL/source-cachemetadata finishingplan; actualhost/native/compiler0 untilleadreview. A cef39accepted87-cellClaimsranges independentlyreviewedsourcepacket, no nativeinitialization/totality/effect orcoherentcallerclosure. Port34 actual360failedentrybeforeIO;361onequalified-entrycorrectionfromsoundnesscarry,no privatebudget. Bothsecuritytargetsnotyetestablished; privatebudgets/allnative-E1/world/errors/drop/controller/transcript/L1L2L3/client/artifact/performance/adoptionobligationsretain.


D226 continuation: separate soundness raw361 PASS5exports/88strictreadbacks, independent1.924107167s/340475904B/swap0 source/data audit, merged/cleaned. No theorem/proof/auditclaim. Port35 focusedstrongCalls plusstrictsame-type/minimal-reference Bridgeproofrepair MAX2local362/363 fromsoundnesscarry, reservedtwoenclosingconsumer calls untouched; no private/host/nativebudgetborrow. SbfRuntimeFinish64929 verifiedlive/sourceonly. All native/world/E1/drop/controller/Claims/Terminal/transcript/L1L2L3/client/performance/artifact/adoption gapsretain. Bothdeployedtargetsnotestablished.


D226 continuation: SbfRuntimeFinish source-only9e48 reviewed/independent35fixtures+98pathliteralplan/fullguard+payloadassembly PASS1.109512750s/58458112B/swap0, mergedea31c002c2/cleaned. NEW SbfRuntimeAcquire ONE finite metadata SSH executesexactreviewed145492B payload only,115s/120s/512MiBguard/4MiBoutput; noactualtracer/tracee/root/ns/backend/native/compiler/probe/ELF/privatebudget. Nohostretry/retraceoroldGO. Unused fixed_backend_body gate distinguishedfromactualproducer_fixed_body path; missingapprovalruntimepin/disabledentries/adoptiongate remain. Bothsecuritytargetsnotyetestablished; allnative-world/E1/drop/controller/transcript/L1L2L3/client/performance/artifact/source/refinementgapsretain.


## D227 — Separate final private Kani admission from privileged SBF validation (lead, 2026-10-25)

MIRcurrentdcc packet/FINAL-SLOT rereviewed: paired_coordinate_native_resume remains actualnextcomponentgate, Kani59/60final1reserved; ordinaryMIRcfgexcludedharness. FinalNativeGate SOURCEONLY ownparkedproverbranch prepares concretefixeduser-level freshfulladmission plusliteralKani producer, disabledentry, no abstractGOcallback. No rule requiresprivilegedSBFrootfs forordinaryuserKani; full3G4G/Swap0/Tasks64/55reserve7guard2/rawvisibility/source-tool-identity-control policy remainsunchanged. ALLactualhost/compiler/Kani/Rust/Lean/extraction/backend/native/root/ELFbudgets0 inthispreparation; lastslotnotspent. Pendingtypednativeeffect/world/E1/controller/Claims/Terminal/transcript/L1L2L3/client/performance/equivalence/artifact/adoption/release gaps unchanged. Bothsecuritytargetsnotyetestablished.


D227 continuation: SbfRuntimeAcquire actualONE SSH0 nowreviewed/independent3427data checks/fourderivedbyteidenticaloutputs PASS1.637106625s/31555584B/swap0.98paths/82physicalpins/92row35655597Bfiniteinputcandidate, exactSSLconfigpincomplete/noSTALE; hostRSS40484864B/swap0, noGO/cgroupobserved/rootfs/runtime-securityapproval. Botholdfailures/sourcecache/openFD/native/fullruntime/control boundariesretain. SeparateQuery31stronganchor+minimalBridgeproofnormalchecked363 reviewed/independent0.436894542s/152993792B/swap0/three standard-onlyaudits, merged/cleaned, no privatebudget. Port36SOURCEONLY guardedcheckedCItransport/enclosingconsumer preparation, no364. FinalNativeGate70807sourceonlylive, lastKani59reserved andallprivatenative/world/E1/controller/transcript/L1L2L3/client/performance/artifact/releaseobligationsopen. Bothsecuritytargetsnotyetestablished.


## D228 — Review fixed native producer before spending last Kani slot (lead, 2026-10-25)

FinalNativeGatef56 fullsource review/independent28mocktests+6bundle/functionidentity andnewcleanupfaultcheck0.884640792s/40714240B/swap0/nohost/compiler/Kani. Confirmedparent_cancel_child error skipsremainingcleanup/guardfinish/terminal; _tree/filepinsunboundedwholefile/symlinkwalk, freshfivepinfieldsnull/setupsourceunsupplied, newemptycache/profilecompatibilityunassessed. CandidateUNMERGED/UNREADY, no operational/native/semanticclosure. Source-onlyfix/setup continuation addressesconcretecounterexample/finitehashing/owned-scopecleanup/cacheprofile andactualmetadata-preparationsource; bothentriesdisabled, no actualquery/compile orlastslot. Kani59/60finalreserved,Lean240/260,Rust2/3charges(actualordinarybuild1),extraction54/56,backend15/16,ELF0/3 unchanged. Alltypednative/model/world/E1/controller/transcript/L1L2L3/client/equivalence/performance/artifact/release obligationsretain; bothtargetsnotyetestablished.


D228 continuation: separatePort36source29DATAchecksreviewed, missingencoder/root-before-import admissionfoundprecompile. ONEsoundnesscarry364fixedsyntheticnormalcheckedprivate-True/publicimport/fullstrictkeyset/preludeprobe allocated, no actualR1wholeconsumer/host/privatebudget. FinalNativeGatefix/setup77362sourceonlylive, lastKani59reserved/allnativeeffect/world/E1/controller/transcript/client/performance/artifactreleaseobligationsretain. Bothsecuritytargetsnotyetestablished.


## D229 — Native source repair reviewed; concrete lifecycle/setup completion


### Lead addendum — 2026-10-25, native repair review and lifecycle continuation

Immutable dc20aedeee source repair reviewed fully. Independent evidence/lead-review-20261025/final-native-repair-v1.json reproduces22 focused mock/synthetic checks, six immutable policy bundle identities, plan seal and byte-identical source manifest/function/diff reports: exit0,1.322899875s,115245056B child peak RSS/swap0. No host/compiler/Kani/Lean call. Cancellation OSError now reaches independent cleanup/failed terminal. Finite catalog/streaming source/native hashing and separate1GiB setup policy are concrete source progress. Original28 evidence reused; no native or security closure inferred.

Candidate still unready: unconditional SCOPE_UNRESOLVED after any child spawn, setup clean environment/bootstrap/full-interval source/native stability incomplete, fresh runtime/alias/library/cache data missing. SAME candidate remains unmerged. Source-only continuation allocated fixed owned-unit lifecycle/handshake/verified shutdown and concrete candidate-data setup collection, with all actual host/native/compiler budgets0, disabled entries and final Kani59/60 slot reserved. Unknown native roles may be reported as candidate DATA for review; they are not permission or final pin approval. No permanent placeholder accepted as completed producer. Exact prompt archived in worker-prompts-20261025/prompt-finalnativegate-lifecycle-20261025.txt. Private budgets unchanged; both deployed targets NOT YET ESTABLISHED.


## D230 — Concrete lifecycle review; inside-admission ordering repair


### Lead addendum — 2026-10-25, lifecycle review and metadata admission-order repair

Immutable b34142b016 source lifecycle/candidate collection reviewed fully. Concrete parent handshake/invocation-start-cgroup-FD binding, descriptor-wide cancellation/empty-or-removed terminal observations, independent cleanup telemetry, bootstrap seals/finite aliases/candidateDATA collection replace the old unconditional unresolved placeholder. Independent37mocktests/sixpolicybundleidentities/seals/exactmanifest005/functiondiff005 PASS1.248356291s/self34111488B/maxchild115261440B/swap0, nohost/compiler/Kani/Lean. Old22/28 reusedonlyashistoricalevidence. ExistingOS/systemd/procfs/Python/compiler/Kani trust remains; actualkernel/permissions/nativebody semantics notproved.

New explicit lead ordering counterexample: setup._collect reaches candidate acquisition before either fullinside-scope admission or actualcontrols check. Candidate data/native/sysroot hashing mustfollow freshinsideadmission; finalGO/control+intervalstability stillrequired. SourceNOTreadyforexecution. SAMEworktreeSOURCEONLYfix allocated, plus exactprospective DATA-only transfer/activation release forsubsequentleadreview. Maintainedentriesstilldisabled, allactualhost/setup/native/compilerbudgets0/finalKani59/60reserved. No SBF/root prerequisite, no extra trustwaiver, no capraise. Upstreamsystemdv255show/notfoundsourcechecked (notinstalledbinaryidentity), no speculativeAPIpatch. Exactprompt andindependentreceipts archived. BothdeployedtargetsNOTYETESTABLISHED.


## D231 — Finite source review; installer success contract repair


### Lead addendum — 2026-10-25, SbfFinite source review and installer exit repair

Immutable d39aa80a9a finite92-row probe/exclusive-copy installer/dormantsealedentries reviewed. Independent30synthetic methods/276source-pin-importchecks pass; everyrecordedimmutableinput/20a renamedbaseline verified, source regeneration/fullstatementdiff/installationinventoriesbyteidentical. Exit0/1.892669s/self24805376B/maxchild115720192B/swap0; noactualhost/root/native/probe/install/compiler. Exactcapturedguestbody/argv/envunchanged;92clones35,655,597B allaccounted. FullProducerapprovalgates unaffected; finiteOPERATIONAL_PIN=() andallpublicdenialsremain. No kernel/runtime/securityclosure inferred.

Concrete lead counterexample underexplicitmocks: fixed_install successdict is returnedthrough dormantinstallerentry intoSystemExit; successwouldbereportednonintegererroraftermutatingsealcopies. SOURCEONLYrepairallocated sameWT: boundedfixedroot-ownedinstallationreceipt + normalinteger0 installerentrycontract, actualfailuresnonzero/partialretained, regeneratednoncircularentry/package/bootstrap pins andnewfocusedtests. Candidate remainsunmerged/unactivated; noinstall/rootauthorizationorpermissionquestion. Freshoperationalroles/maps/limits/controls/authenticateddeploymentandactualkernel/LSM/lifecycle/source/refinement/artifactjoinsremainopen. Independentreceipts/promptarchived; bothtargetsNOTYETESTABLISHED.


## D232 — Reviewed DATA v3; one bounded ordinary-user metadata action


### Lead addendum — 2026-10-25, exact v3 review and ONE bounded DATA allocation

7717cea252 exactv3source/activation/transfer/payload reviewed. Independent8ordering+14receiver+6activationtests,008manifest/function/diff regeneration and49-artifactfreshreproduction PASS2.580781917s/self51200000B/maxchild115261440B/swap0. Exactly44pinnedfiles/twosetup-onlymains/fourregeneratedsealfiles; FINALmainsdisabled/7freshfieldsNULL/nochargeauthority. Receiver644871B/sha35092a375a438c7ae92cd643d3c9a261f96f7f870b04fc55b17b7a975dd7b0e4/root938d8ef30be641940233c564301517c322fe0b2170c77ee7c12dc5976307a145.

ONE reviewedfixedtransportSSHcandidateDATA action allocated in sameWT afterprecommit/actioncharge. Ordinaryuserfresh0700sourceleaf only; no root/privilegedSBF/compiler/Kani/nativeproof/cacheadoption. Actualfreshfull1Gprospective/inside/GO policy/768MHigh/Swap0Tasks64/512MiBresident115s/120stransport4MiBoutput unchanged. ConditionalONEread-onlyfixedunitstatusSSH allowed ONLYiftimeout/missing/unresolvedterminal, no workloadrestart. SSHexitnotremoteclosure; actualterminal/errors/unresolved/controlreceiptscontrolinterpretation. Minorparentterminal.failed precomputedbeforeearlierreceiptwritefailure retainedrough edge: nonzeroexit+errors authoritative, fixbeforefinalproduceradoption. Sourcev3frozen/nochangesallowed. Noownerpermissionneededforordinaryuser metadata alreadywithingoal. Allheavybudgets0/finalKani59/60reserved/Lean365counterunchanged. Independentreceipt/promptarchived; bothtargetsNOTYETESTABLISHED.


## D233 — Installer source repair accepted; DATA ancestry rejection retained


### Lead addendum — 2026-10-25, installer repair merged; loader counterexamples and host ancestry diagnosis

SbfFinite 48618be4a3 source repair reviewed and independently accepted: four new actual-entry/OS-mock tests, 279 immutable source/pin/import checks, 159 repair checks and byte-identical report/source regeneration PASS. Lead review 2.917471208s, self 21,528,576B, maximum serial child 189,890,560B, swap0; concurrent aggregate unobserved (conservative peak sum recorded). Worker coherent 34-case suite reused with exact final source pins. Dormant installer now calls fixed_install_entry()->int, writes one exclusive bounded durable root-owned installation-only receipt, then returns0; copy/seal/receipt failures propagate and retain partial paths. Internal dict preserved; other user/root contracts and captured 92-file guest/body/env unchanged. Merged 50fdc4f365 and immediately removed accepted clean worktree/branch. Public denials and OPERATIONAL_PIN=() remain; no actual install/root/native/kernel/security approval. Fresh operational roles and authenticated administrative publication remain open.

Port36 ff850f3f1e returned concrete full R1 source, 13 monitor mocks and one earlier-source own sleep2 SIGTERM control fixture. Full new source review found three concrete blockers: stale unresolved Port35ANCHOR_Select.unwrap in self-contained Delta/FullDriver/TinyNext; a diagnostic write aimed at retained read-only Port35 evidence; monitor tracked only same-PGID descendants. Independent immutable mock counterexample confirms an observed different-group descendant survives root reap while lock releases at0.2s before mock descendant disappearance0.4s; original13 mocks still pass. Lead review0.085613584s/self22,085,632B/swap0, no compiler/process control. SOURCE-ONLY correction plus concrete minimal header/API preflight source assigned PID93454, no new fixture/compiler authority. Actual365/368 unchanged, last carry366 and whole-consumer367/368 unallocated. Full ~1.97GB pinned core arrays/multiple mapped region sets have unestablished8GiB feasibility; no full-core rerun or unchanged rehash authorized. Exact type/value inverse guards, normal kernel/Elab/all-aux replay, complete axioms and caller statement boundaries retained.

FinalNativeGate one actual DATA action a29e6496d8 failed at pre-install ancestor check: SSH/receiver exit1,1.885524208s, stderr248B, sampled local aggregate62,832,640B/swap0; no leaf creation/setup/admission/runtime collection reached. One allocated conditional status SSH exited0, observed fixed unit not-found/inactive/dead with empty invocation/cgroup. This is evidence for this action/observation, not universal kernel control or remote resource enforcement. Exact source/payload/seals unchanged; independent immutable review PASS1.389170333s/self21,430,272B/max serial child6,127,616B/swap0/nohost calls. Rejected ancestor/field still unknown; Mac firewall/port causation not established. ONE new finite READ-ONLY fixed stat query of six literal ancestor/leaf paths allocated PID92525 (20s/64KiB/strict SSH/no retries/no config or permissions changes). No new DATA install/proof/compiler action allowed until cause reviewed. Final Kani59/60 remains reserved; both deployed security targets NOT YET ESTABLISHED.


## D234 — Remote ancestry predicate identified; private path candidate preparation


### Lead addendum — 2026-10-25, observed group-write rejection and private path source repair

One finite ancestry query c67d0a3d5a returned536B, SSH exit1 due missing literal leaf,0.650162s; sampled Python+SSH RSS27,984KiB/local swap0. / and /home are root0755; /home/dombarker UID1000 mode0750; project-offloads and its assigned project child UID1000 mode0775. First observed failing predicate is group-write020 at project-offloads; no historical immutable-chain or Mac hardening causation inferred. Two failed local AS/RSS setters happened before ledger/SSH, retained with missing historical metrics; changed sampled capture spent exactly one query. Independent immutable data/predicate/source-boundary review PASS0.164392541s/self20,348,928B/max serial child6,684,672B/swap0/nohost.

Source-only v4 release preparation assigned PID94738 in retained prover candidate. Proposed fixed stage /home/dombarker/final-native-gate is a direct child of observed secure home; leaf existence remains unobserved and receiver must refuse any preexisting entry. No parent/config/permissions changes, no new SSH/install allocation. Historical v3 untouched; v4 explicitly re-pins only staging-bearing source/payload/manifest/seals and fixes terminal.failed write-order propagation under fault tests. Existing target/harness/cache paths remain unchanged. Full ordinary-user1G admission/controls/ordering/strict55 reserve7 guard2 and disabled FINAL entries preserved. Lead review of exact new release precedes any newly charged DATA action; final Kani59/60 still reserved. Port36 source repair PID93454 continues without compiler366 authority. Both targets NOT YET ESTABLISHED.


## D235 — Private-stage DATA v4 reviewed; one bounded transfer allocated


### Lead addendum — 2026-10-25, private-stage v4 reviewed and one DATA action allocated

ce3fa578fe/source3e4b5df592 full new v4 source/release review accepted. Only staging-bearing constants/functions move to /home/dombarker/final-native-gate; existing native roots, target/harness/registry/cache locations and all other plan fields retained. Parent terminal constructed after prior cleanup/guard writes now reflects their errors/unresolved; maintained and FINAL mains disabled. Historical v1/v2/v3 unchanged. Independent clone22 v4+8 ordering mocks, complete changed-function statements/nonstage plan identity and51-artifact fresh byte reproduction PASS2.448144083s/self26,705,920B/max serial child92,094,464B/swap0, nohost/compiler. Exact46-file payload/receiver674071B sha18e242703d5603f89c6b5e09fb69484861936eca11e435b7fdd38f74323dd1cd/transport3854B sha58a97be919d40605bc6eef5f1263ed5847eb5467b419dbad0cc09f4a19ef6b72/root4868d7071dca1eb6eebfd81d7db74bc899b643441cda2d1f159ea854ecb551de verified.

ONE new exact v4 transport DATA action allocated PID97199 after review/precharge; optionalONE fixed-unit status SSH only for missing/unresolved terminal. Fresh leaf must be absent/no adoption; all owner/nonwrite/nofollow/FD/exclusive/private-copy/seal checks preserved, no host config/permission changes. Full1G prospective/inside/GO admission and actualcontrols/order/strict55 reserve7 guard2/512MiB resident115s/120s4MiB bounds unchanged. No finalKani or other compiler/native/root authority. Actual result pending; final fieldsNULL/Kani59/60reserved. Port36 focused366 PID96092 pending. Coherent caller/SDK/runtime/extraction/artifact and both deployed security targets NOT YET ESTABLISHED.


## D236 — DATA setup failed with rejected receipts; private publication counterexample retained


### Lead addendum — 2026-10-25, actual366 failed indexing; v4 transfer reached setup but receipts rejected

Port36 actual366 at505ec72a6b failed elaboration: array ! access requires Inhabited(ModuleData x CompactedRegion), shared by full Transport. No serialized header/import/reset observation or theorem established; diagnostic error-recovery sorry abort retained, no source sorry added/evaluated. Exit1/wall7.584792167s/process1,269,923,840B/sample aggregate1,308,508,160B/swap0. Reap completed/lock released; one identity mismatch lacked the rejected row, cause UNKNOWN. No signals sent. Raw generic monitor compiler_calls0 is not a ledger: actual durable charge+SPAWNED prove1; corrected interpretation actual366/368 with ONLY367/368 reserved/unallocated. All finite pins unchanged. Independent immutable source/log/event/pin review PASS0.224579500s/self21,954,560B/swap0/noCLI. SOURCE-ONLY repair assigned PID98524: optional/proof-bounded region access, recorded rejected identity evidence and concrete public-API/memory ownership review. No new compiler/header call or unsafe default/freeing. Current full1.97GB byte arrays/multiple region sets8GiB feasibility unestablished; reserved calls await source admission.

FinalNativeGate v4 b5b4339499 reports exact46-file525933B/root transfer, then setup_exit78. Childterminal/candidatecontrols missing; all3parentrecords rejected by regular/singlelink/owner/writebit predicate, so actual underlying error, file modes, admission/headroom/runtime/controls remain UNOBSERVED. Main3.163327791s/self21,692,416B/sample aggregate52,002,816B/swap0; ONE allocated conditional query0/.635927s observed fixedunitnot-found/inactive/dead/emptyinvocation+group. No universal closure or setup success inferred. Immutable review verifies source/payload pins/root/allreturnederrors/counts/status. Independent actual _publish local filesystem counterexample under own umask002 creates0664, rejected by original receiver mode&022 check; actual host umask/mode remains unknown. Review0.818482208s/self23,412,736B/swap0/noSSH/setup/compiler. No source assumption discharged.

SOURCE-ONLY continuation PID99348 prepares exact3-file nofollow/bounded read-only diagnostic for separate lead approval and explicit0600 exclusive durable publication fix with umask/failure tests. Existing remote v4leaf/payload untouched; no overwrite/delete/adoption/retry/new host authority, no v5 release yet before cause known. Group-writable file content if collected is explicitly untrusted diagnostic DATA, never GO/pin/execution approval. FinalKani59/60 remains reserved. Both source jobs retain all SDK/std/runtime/allocator/extraction/native/source/artifact/security boundaries; both deployed targets NOT YET ESTABLISHED.


## D237 — Private receipt source validated; one finite read-only diagnostic allocated


### Lead addendum — 2026-10-25, optional indexing/identity repair reviewed; bounded owner reuse and receipt query

Port36 dc6f1d3c14 source reviewed: region-owning array ! replaced by optional rejection/direct iteration; semantic Checked/Delta/Consumer/FullLoader unchanged. Monitor excludes descriptive comm from hard root identity while retaining PID/PPID/UID/GID/PGID/birth, exact Popen/runtime admission and all lock/control/reap requirements; rejected row/required identity/literal poll are recorded before any control. Actual366 mismatch cause still UNKNOWN. Independent16 baseline+10 new mocks pass(.014110500s/23,314,432B/swap0);55 preserved files and finite owner arithmetic verified(.020058334s/37,109,760B/swap0). Lead preservation path assumption failed first (relative paths mistaken for absolute); failure retained, only collector changed and26 mocks not repeated. No new Lean/host/control call.

Memory table identifies five retained core representations totaling9,851,882,880B in file/payload extents, explicitly neither an RSS lower nor upper bound;8GiB feasibility remains unestablished. SOURCE-ONLY concrete byte-binding/authentic public opaque ImportState and held raw-guard reuse refactor assigned PID1483. It must preserve complete normal importer/finalizer/initializer semantics, all-level guards and all Kernel/Elab/CI/axiom/caller obligations; no private state access, fabricated metadata, unsafe freeing or new logical callback premise. Stricter heap cap may be proposed, no cap raise. Whole certificate aggregation must use the dedicated Linux host per AGENTS, with fresh pinned workspace/runtime/ABI and capped admission; no host/toolchain action authorized by this source task. Actual366/368;367/368 remain reserved, no further local full replay allocated.

FinalNativeGate receipt source8f2d92ffbe fully reviewed. New explicit0600 exclusive relative private-packet writer handles short writes, identity/fsync/failure retention; all five publicly consumed JSON names use it. Current maintained source remains UNSEALED/not ready and v4 payload unchanged. Fixed read-only diagnostic/payload7520B SHA23572ac049dc7cdd782ed6880aedee4fbf40d604d04db3030f0c85dae10a7cf0 and disabled transport7266B SHAe226fed2a479af969c4930b07d59c766e72440b37d33bb0e745b767603395fa5 reviewed. Independent12 publication+9 diagnostic+4 mocked transport cases/current seals/function regeneration PASS1.137077709s/self21,200,896B/max serial child102,793,216B/swap0, noSSH/setup/native/compiler.

ONE exact three-parent-record read-only diagnostic allocated PID2623 after precharge. Literal nofollow ancestor/file scope, eight FDs,1MiB/file3MiB total, terminal parsed only<=64KiB, cleanup/guard hashes+metadata only, original receiver predicate recorded unchanged. File group-write debug exception yields explicitly UNTRUSTED DiagnosticBytes only; drift denies interval, no approval/GO/pin/content execution or stage writes. Remote10s/local20s4MiB/sample512MiB, no otherSSH/retry/config/permissions/setup/nativeproof. Future transport faults may leave missing local receipt; preserve uncertainty rather than infer cleanup. Actual cause/modes/umask remain unknown until result; no v5 source release/upload allocated. FinalKani59/60 reserved. All SDK/std/runtime/extraction/source/artifact/security joins remain explicit; both deployed targets NOT YET ESTABLISHED.


## D238 — Receipt diagnostic records prospective denial; decision data still missing


### Lead addendum — 2026-10-25, actual receipt query identifies prospective denial; Linux runtime probe source

FinalNativeGateReceiptAction ee8335334c exactly one read-only SSH exit0,0.907253500s/self21,725,184B/SSH5,111,808B/sample combined26,492,928B/swap0/output2995B. Reader reports stable intervals/no errors; all3parentfiles currentregular UID/GID1000/nlink1/mode0664, all original receiver predicates false; content remains UNTRUSTED DiagnosticBytes. Terminal reports failed=true, errors setup prospective admission denied and two scope ownership unbound; unresolved=false is not closure. Current file mode is observed, actual umask/historical state/decision reason not. No setup retry or stage modification. Independent immutable packet/manifest/sourcepins/counts/predicates/complete terminal review PASS0.404149625s/self20,414,464B/swap0/noSSH/Lean. Formal assumptions unchanged, all native/runtime/source/artifact/security obligations remain open.

SOURCE-ONLY bounded prospective-report.json decision diagnostic assigned PID3820 in retained prover worktree. It must read one exact existing report<=2MiB, return only bounded decision/collection-failure semantic fields plus metadata/hash as untrusted data; no full raw process/env/ordered data, parser authority or newhost call. Existing011receipt diagnostic and all historical v4 evidence frozen. No v5 stage/release/setup allocation until actual reason known; publication fix remains UNSEALED/not ready. FinalKani59/60 reserved.

New isolated LeanHostProbe SOURCE-ONLY job PID4739, WT.worktrees/cx-lean-host-probe branchcodex/cx-lean-host-probe-20261025 baseb2c335bc89, prepares finite read-only dedicated Linux Lean4.32 runtime/API/Prelude/historical-workspace metadata query. Literal paths, bounded shallow toolchain names and streaming hashes only, no compiler/version/help/install/coldbuild/host call. Mac/Linux version labels do not imply byte identity, portability, Core6060 or initializer equivalence. Any full generated-certificate replay must use dedicated Linux host with fresh pinned runtime/workspace/ABI and capped admission per AGENTS; current host readiness unobserved. Port36 concrete byte-binding/public opaque state/raw-owner reuse source PID1483 remains live. Actual366/368 with367/368 reserved. Three owned CLI workers, no collaboration subagents or A-file access. Both deployed targets NOT YET ESTABLISHED.


## D239 — 2026-10-25: bounded admission query and Linux runtime observations

Admission reader6122c94ec9 independently passes14 fixtures/full function regeneration/seals(.809343500s/self20,365,312B/maxchild102,809,600B/swap0). ONE actual e8ffe0b688 report query exits78: stat14,107,502B exceeds fixed2MiB; zero bytes read/full hash and reason UNKNOWN. Actual .811681459s/self22,331,392B/SSH4,816,896B/sample27,082,752B/swap0/output1853B. Independent immutable action review PASS. No retry/cap raise/generic streaming parser. Compact future admission semantics/private publication/truthful no-spawn source-v5 worker8798 returned12789a821e terminal0; lead review pending, no new setup action allocated. Final Kani59/60 reserved.


No private source/refinement assumption discharged. Compact-v5 source12789a821e returned, not yet accepted or allocated; original14MB denial reason unknown. Native/sourceDrop/E1/L1/L2/L3/SDK/std/runtime/extraction/artifact joins and both deployed targets remain open. No Kani charge;59/60 final slot reserved. See coordinator addendum and archived exact prompts/independent receipts.


## D240 — 2026-10-25: v5 source review and one DATA allocation
FinalNativeGate12789a821e/source020 fully reviewed. Compact117-line projector selects actual decision booleans/numeric budgets/errors/failures <=64KiB without raw-tree traversal; unknown/projection/publication faults retain failure. Same-execution not_started plus absent child/pidfd/identity/scopeFD/binding skips unbound scope methods truthfully; uncertain/owned paths retain control/reap/monitor. Shared private0600 publisher covers raw save, old limits retained. Exact fresh /home/dombarker/final-native-gate-v5-20261025 refuses all existing entries. Policies/adapters/guard/runtime helpers unchanged; source/FINAL mains disabled/seven fields NULL. Independent23 source+19 release fixtures/source audit/full source/payload/function report pins/nonstage fields/historicalv1-v4/fresh byte reproduction PASS. First lead collector schema equality assertion failed after successful fixtures/reproduction; summary is a proper subset of release with no conflicting field. Failure/logs retained, first fixture metrics UNKNOWN; replacement source-only validation .470757709s/self25,542,656B/maxserialchild6,356,992B/swap0, no fixture rerun. Receiver877610B SHA2aec50ced21005cfb6117bb83f4670ba56f703ab0b55840e793091be7c410835/transport3854B SHA5f397a25a3873755b58f97400cb336bae065dae9681df6a2f34c43f21964f3dd/root63d1c9087fe936618d506f7c1c6dcb01a1222973f2e022df892d10cfcbff0032.

ONE actual v5 DATA action allocated PID12681 only after review; pending. Exact fresh leaf/payload/1GiB metadata scope/strict55 reserve7 guard2/full visibility and both identity scans/inside actual controls before acquisition/fullGO/stability unchanged. Main1 plus conditional fixed-unit status0or1 only for missing/unresolved/timeout terminal, no retry/otherquery. All final/native/proof/compiler authority0, Kani59/60 reserved. Old14MB denial reason still UNKNOWN; no environment/bus/capacity/Mac attribution.

Port36c0da01870c fixed Linux source preparation fully reviewed. Independent40 source/synthetic cases+all generated byte reproduction/package pins/unchanged four logical bodies/enumerated FullLoader literal changes/binding functions/monitor/Rss bundle adapter substitutions PASS1.732020208s/self75,464,704B/maxserialchild99,991,552B/swap0, no host/raw/core/Lean. Caller and publication unconditionally disabled, runtimeMISSING; this is not execution readiness. Lead tiny own-file counterexample confirms stage.stream_copy leaks sourceFD if destinationO_EXCL fails (opened1/closed0; originaldest unchanged; lead closed only ownFD afterward). Source-only continuation PID13821 repairs FD acquisition cleanup, makes total hash+ELF actual-read budget explicit, adds meaningful synthetic ELF/alias tests and prepares exact disabled one-query transport/payload. No host query or staging allocated. Current actual366/368;367/368 remain reserved. Whole core/project serialization/runtime/ABI/admission/control/capacity/peak and coherent caller/security/artifact joins remain OPEN. No logical assumptions/trust/contract/frozen artifacts changed; both deployed targets NOT YET ESTABLISHED.


## D241 — 2026-10-25: v5 procfs guard failure retained; source correction
FinalNativeGateDataV5Action0f17eee7c8 reviewed from immutable source and all returned semantic fields: exactly mainSSH1/conditional0, receiver reported68files686052B/root63d1c9087fe936618d506f7c1c6dcb01a1222973f2e022df892d10cfcbff0032 transferred. Setup/SSH/transport78, transport2.188204542s/local22,069,248B/swap0/errors[]. Parent failed=true/spawn_state=not_started/unresolved=false; admission unknown/allowednull/reporting_failedtrue after watchdog ProcessLookupError errno3. No setup Popen attempted in this execution; no systemwide absence/cancellation/general kernel closure inferred. Childterminal/controls missing as expected; conditional status not authorized. Guard/cleanup contents not fetched, only size/hash; exact failing syscall/PID and remote metrics UNKNOWN. No capacity/env/bus/Mac-port conclusion.

Local evidence caller failed after samePID/starttime became RSS0/<defunct>: mutable command-label equality raised identity drift before poll; callerexit1/savedchildexitnull. Actual transport receipt78 retained; finally Popen.poll reaped, no group signal. Caller2.371357999s/self25,690,112B/sample56,328,192B/serialchild102,432,768B/swap0, serialchild includes Git/ps preparation. Immutable independent review verifies72 source/payloadpins, exact68-file count/bytes/root, frozen source diff/all26sample sums/terminal/metrics and two synthetic ESRCH source counterexamples PASS1.091180167s/self30,457,856B/swap0/nohost/Lean. Proc.optional identity and Proc.children task read propagate ESRCH even with independently verified absence; these source cases do not identify the historical failing syscall.

SOURCE-ONLY continuation PID15067 repairs genuine ENOENT/ESRCH handling only after independent matching proc/task absence, keeps live unreadable/reuse/unknown/permission failures closed, records exact operation context, and repairs local caller poll/reap/exit persistence with descriptive comm. It also prepares a fresh v6 release, preserving v1-v5 and all strict policy/compact/private/no-start guards. No new actualSSH/query/setup/retry/native/compiler allocated; finalKani59/60 and soundness367/368 remain reserved. Port36 Linux runtime transport/FD/budget SOURCE worker13821 continues. No security premise/trust/contract/frozen artifact change; all source/runtime/extraction/native/caller/artifact joins remain open and both deployed targets NOT YET ESTABLISHED.


## D242 — 2026-10-25: v6 producer/cleanup join rejected before execution
Private v6 source018e9d2aff returned, review partial. Guard/caller/receiver/builder/bridge source inspected, no acceptance or actual allocation. Concrete producer/consumer join counterexample: new Proc.cancel returns verified-disappeared, unchanged cleanup accepts only disappeared/verified-owned-signalled, so verified gone child becomes false unresolved error. Independent mock-only realProc->Guard.cancel_owned->cleanup counterexample PASS .002980875s/self29,884,416B/swap0/nohost. First fixture patch failed on Mac missing Linux os.pidfd_open; create=True mock corrected fixture only, source unchanged. SOURCE-ONLY narrow compatibility repair PID22322 preserves independent absence proof, stable identities and control failures, restores compatible outcome and adds actual cleanup bridge tests. First unuploadedv6 candidate must be preserved before explicit supersession/re-pin; v1-v5 historical/actual bytes stay unchanged. Kani59/60 reserved.

Owner asks why ten hours/why old launcher stopped and whether8GiB became2GiB. Lead has NOT established old launcher failure; new launch/monitor defects must not be attributed to old route or Mac ports. New immutable-history forensics worker18652 in isolatedcx-launch-history investigates latest verified successful NUC invocation/launcher/receipts and exact changed path/policies, no host/Lean action. The new Lean whole-job cap remains8GiB; internal-M3200 was proposed down from4400 to leave room for mapped core/startup/other allocations, and remains UNVALIDATED, not a measured fit. Separate metadata/diagnostic limits do not establish an8-to2Lean change. No new NUC wholeconsumer has started. SSH success/standardLean4.32 files observed; none of the recent private DATA errors demonstrates Lean or firewall failure.

Three bounded SOURCE/history CLI workers live; no collaboration subagents, no A live-file access, no new host/compiler/native/proof calls. Coherent caller import/re-pin, runtime/SDK/std/extraction/allocator/native/artifact/security joins and both deployed targets remain NOT YET ESTABLISHED. Security contract/frozen pins unchanged.


## D243 — 2026-10-25: v6 source accepted; actual DATA denial precedes setup

FinalNativeGate v6 source022/bbd110029f has an independent passing8-case concrete producer/guard/cleanup bridge,1 changed cancellation predecessor and10 lifecycle/order review, preserved beforeimage/releases and byte reproduction. Prior verified-disappeared consumer mismatch was repaired without relaxing absence/identity/control failures. Root evidence/lead-review-20261025/launcher-recovery-v1/privacy-v6-source-review.json retains exact pins/metrics.

ONE actual DATA resultc4a4816d93 transferred68files691075B; SSH/setup78, main1/conditional0, source/helper mains remain disabled. Compact report truthfully says failed/not_started/unresolvedfalse, reporting_failedfalse, allowedfalse. Both resource snapshots rejected pids membership/current mismatch; actual node/counts UNKNOWN. No setup/native/Kani/Lean/Rust/ELF began, no capacity/ports attribution. Existing remote private guard/cleanup and >5MBraw reports retained hash/size only. FinalKani59/60 remains reserved; seven native fields NULL.

The shared resource candidate has a narrow Port36-only correctionfe3e168917: visible live task count<=charged pids.current, retaining cap checks/no memory credit.16old+10focused pass. The subsequent actual Port36 publication49f36dfb1b completes both scans but is denied on the existing conservative memory formula by5.378GiB; not the same PID defect. Privacy v6 bundle/remote leaf unchanged, no v7/retry allocated. Offline five-minute numeric-policy review37614 only; no host authority. Both deployed targets NOT YET ESTABLISHED and all E1/full real refinement/L1/L2/L3/cleanup/native/artifact/absolute speed gates remain OPEN.

## D244 — 2026-10-25: resource admission passes; catalog exclusions now explicit

Privacy v7 entered setup but failed the old global task-count check. Updated v8-r3 passed prospective AND inside-scope resource admission. Exact68files696048B transferred; setup exit78 after2.752526521s/54,736KiB/swap0. Collector says507fixed source paths unacquired; that does NOT show507files absent:49transferred-stage files were outside its ADMITTED roots and775ancestors stopped cargo/project source reads. Only two speculative library roles were observed missing. Lead fetched the exact459693B partial report under a separate bounded read-only allocation. Conditional fixedunit status is not-found/inactive/dead; parent controller failure remains retained, no universal orphan/control closure. No native/Kani/compiler ran. Kani59/60 remains reserved. Source-only worker62004 investigates this concrete catalog obstruction without changing host permissions or weakening finalnative checks. The earlier r2 local receiver path/pin mismatch was a lead review omission, preserved and corrected before r3; it started no SSH.

Both deployed targets remain NOT ESTABLISHED. Contract/frozen Rust/ELFs unchanged; actual source-to-model, SDK/std/runtime/extraction/allocator/native/adaptive privacy and coherent import/artifact joins remain explicit. Claims parent review is partial and must not be promoted to native/security closure. Current accepted common-source evidence is root; Port36 and prover branches remain unmerged candidates. Next concrete deliverables: reviewed370 indexed-driver run under unchanged limits, and a truthful privacy catalog result separating excluded roles from absence.

## D245 — 2026-10-25: v9 planned source narrows to five observed marker files

Privacy actualv9 retains prospective/inside resourcePASS;507unacquiredpaths narrowedto5existing group-writable .cargo-ok markers, eachmode100664/uidgid1000/size7/nlink1, sameunchangedexpectedSHA. LeadexplicitDATAruling permitsread/hash EXACTfive underexistinginstalledOS/tools/no-untrustedwriter boundary, strictfinalReaderunchanged; no chmod ornewsecurityassumptiondischarge. Source-onlyworker68220 preparesv10, no actual/native grant. Scope parentcleanup stilltruthfullyunresolvedon2ENOENTs; conditionalunitstatusnotfound/inactive/deaddoesnotrepairthatboundary. BothdeployedtargetsNOTESTABLISHED.

## D246 — 2026-10-25: v10 stops at unbound scope readiness

Privacy actualv9 passed both resource checks and narrowed planned source exclusions to five existing .cargo-ok marker files. Source029/v10 permits only those exact five DATA reads with fixed metadata and unchanged expected hashes; strict final Reader remains unchanged. Actualv10 was stopped before collection: its pre-binding loaded/active/invocation/start predicate failed, exact field unknown because the raw row was not persisted. Parent scope ownership remains unbound/unresolved. Conditional status now reports loaded/failed, InvocationID28bdad7bd8784522aba44fc8b4b9b45c, emptyControlGroup. No native/Kani/Lean ran, no five-marker runtime validation. Source-only worker71555 investigates bounded startup readiness/evidence retention; no unit reset/stop or new DATA allocation authorized. Earlier parent cleanup ENOENTs are a separate retained obstruction.

Both deployed targets remain NOT ESTABLISHED. Contract, frozen implementation and artifact pins are unchanged; existing source/refinement/native/runtime/allocator/extraction/adaptive privacy and import/artifact joins remain explicit. Two source-only CLI workers are active; no owned compiler/SSH action is currently running. Next concrete deliverables: baseline substep/memory-shape review and truthful scope startup observations, without another unchanged full consumer retry.

## D247 — 2026-10-25: stale privacy stage join fixed; fresh handshake reaches collector

Privacy actualv10 packaging had a concrete mismatch: its Scope.STAGE wasv9 while setup/inside usedv10. The failed raw readiness row remains unavailable; actual child logs are empty, so no specific child instruction is asserted. Lead missed this join in earlier review.03e12c72c3 corrects all active stage roles, including bare receiver leaf names, and permanently makes the builder reject stale scope/receiver stages before publication. Exact source rejection fixtures and byte-identical reproduction pass. An intermediate unuploaded v11 preparation with mismatched paths was preserved privately and rejected before any allocation. The final coherent v11 source/pins were committed before execution.

Lead reset only the failed state of the own v10 unit after matching InvocationID28bdad7bd8784522aba44fc8b4b9b45c, loaded/failed, and empty ControlGroup. Reset returned0; poststate not-found/inactive/dead. No stop/signal/config/permission change or universal orphan-absence claim.

Actualv11 bound its fresh scope and reached the inside collector, confirming progress beyond the old stage mismatch. Prospective admission passed; inside pair failed the unchanged structural equality. A bounded read-only comparison of the exact retained15MB report found two added UID1000session60268/60269.scope nodes,117->119rows, and no other structural field change. Full report stays remote by hash/size. No marker-file hash validation/native/Kani proof ran. Parent cancel/finish ENOENT and scope closure remain unresolved. Source-only worker83218 prepares up to3 entirely fresh admission pairs within an unchanged overall deadline, retaining failed evidence and all checks, rather than accepting a failed pair; no actual retry/native grant.

Both deployed targets remain NOT ESTABLISHED. Frozen implementation/artifact pins and binding contract unchanged. Native/refinement/SDK/std/runtime/allocator/extraction/adaptive privacy/coherent import/artifact boundaries remain explicit. Two source-only CLI workers are active; no owned NUC compiler or metadata action remains running.

## D248 — 2026-10-25: v13 DATA setup and observed cleanup succeed
Privacy source032/1912a56990 fixes the removed-kernfs retained-FD predicate without relaxing scope identity/control checks. Actualv13/a8052c25ff passed setup exit0,7.245683229s,80080KiB RSS,swap0; parent failed=false,unresolved=false and prospective/inside/go resource admissions passed. This is bounded DATA operational evidence, not Kani/native/privacy closure. Installed OS/tools/no-untrusted-writer trust and strict final Reader remain unchanged; native/runtime/cache/control roles still require review. Final Kani59/60 remains reserved. Host repair restored exact existing stronger proof/lib.rs pin f07ab675de0556f5feb518f00050583c9d8b9db2b03d79c9c6b1035c90ac8dc2; only the missing Ghost::coordinate()==j assertion was added. Backup preserves old bytes. Repair exit0,.670410625s, no proof execution or frozen implementation change.

Both deployed targets remain NOT ESTABLISHED. Next: review observed native/runtime/cache/control roles and remaining final configuration before any last Kani grant. No new final proof charge.

## D190 (lead, 2026-10-25 13:05): lead resumes; the Codex-manager period is wound down

From 2026-10-24 10:00 to 2026-10-25 12:30 a Codex manager ran the loop. In about 27 hours there were
about 500 commits, and about 114 of them concerned launcher, admission, metadata, monitor, installer,
staging and memory-policy machinery rather than proofs. Root cause found by the lead: the manager
rewrote the worker Lean rules (scratchpad `local-lean.txt`, 00:16) to `-M4400` with extra pinning,
I/O and deadline rules. Ordinary imports peak at about 4.2–4.4 GB, so compiles hit Lean's internal
4,400 MB ceiling, which was then treated as a host "memory failure". Each failure spawned more
infrastructure review. The build host itself is healthy (52 GB available, low load). Actions: the
lead's rules are restored (`-M7000` inside 6G/8G scopes; workers do not build or repair
infrastructure; on launcher trouble they stop and report). The manager's running job
`cx-port36-transport` was stopped, with a WIP snapshot kept. Proof results the manager merged are kept
(e.g. the concrete Claims parent and S1 finish connection, and Q1/Q2 port modules). Infrastructure
changes are left in place but no longer required by worker rules.

## D191 (lead, 2026-10-26): prover candidate status and its ELF divergence

The proof-friendly prover candidate (codex/cx-prover-rw-20261023, UNMERGED) now has query refinement, entropy/retry modelling (exhaustion 2^-4080 per call and 2^-4077 over eight attempts, as CONDITIONAL model results) and 74 of 262 operation-dictionary interpretations. Conjunct 1 of RustProverRefinement remains a premise. A second worker (codex/cx-prover-dict-20261026) covers the off-path entries. The default ELF built from the CANDIDATE branch's source hashes to d7d42f77..., not the release pin f8c0ec72.... Production is unaffected: lowering2 reproduced all three release pins from research. The candidate branched before the adapter/H5 adoptions and edits shared aspis-core files. Before any adoption it must be rebased onto research, and its effect on the verifier ELF measured; any verifier-byte change needs owner approval. Privacy target not yet established.

## D192 (lead, 2026-10-26): host barrier cap correction for the prover candidate

The prover-candidate host barrier (/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/barrier.py) asserted exactly MemoryHigh=5G / MemoryMax=7G. That rejected every launch at the policy caps 6G/8G (run-joint.sh MX=8), which are required for Lean -M7000. Lead edit (one line; backup barrier.py.bak-lead-20261026): the assert accepts exactly the pairs {(5G,7G),(6G,8G)}, with swap 0 and pids 64. Nothing above policy is accepted, and the reservation scanner is unchanged. Separately, workers follow local-lean.txt rule 6: one scope at a time per job, and wait/retry at the aggregate reservation barrier.

## D193 (Stream B, 2026-10-26 09:20): privacy stream opened; six jobs; dict5 reviewed

Numbering note: D193–D248 above were written during the Codex-manager period (2026-10-24/25)
and Stream A then appended a second D190–D192. Stream B (the privacy lead, a separate Claude
session) continues from D193 with the suffix "(Stream B)"; the earlier D193–D248 are not superseded.

Owner instruction at session start: Stream B may run up to six Codex jobs (the handoff said three).
Six 8 GiB scopes plus Stream A's three exceed the 55 GiB host reservation, so Stream B mixes
host-heavy proof jobs with source-only audits and lets the reservation barrier serialise compiles;
no cap is raised. Env-J IDs for privacy start at 20000.

Jobs running (outputs `codex-pv-*.out`, prompts `prompt-pv-*.txt`): prover-rw14 (inherited, main
path of the candidate), pv-dict6 (dictionary branch, see below), pv-ledger (the mechanical privacy
premise ledger `design/PRIVACY-LEDGER-20261026.md`, same method as the soundness ledger, audit
only), pv-l2-sim (F3/F5/F6 simulatable-trace proofs per D166 on research's R1Z tree, prefix
PV_L2_), pv-rebase (candidate merged onto research in its own branch `codex/pv-rebase-20261026`,
three-ELF identity and the <15 s / +10% timing gates; a verifier-byte difference is a stop and an
owner escalation), pv-client (proof-account route audit per D162 and integration receipt).

prover-dict5 finished (head 8f80a91331, unmerged, unpushed): 163/262 operations selected, 26/28
type representations; Formatter erased from the retry execution and the proof-account caller
(`PDict_FormatterIndependent`, `PDict_ClientFormatterIndependent`); native Debug sink contract
checked for 17 variants; audit J14440 exit 0, 1.92 s, 4,294,736 KiB RSS, swap 0, 176 standard-axiom
reports. Open: std.io.error.Error (dynamic trait payload; extraction rejects it), type 27, File
ownership/world transport, 99 operations. Root conjunct-1 premises removed: 0. Lead review:
no sorry/admit/axiom tokens; the 483 added lines under crates/ are cfg(kani)-only harness modules
(verified by inspection of every added module head), so no shipped bytes changed; the candidate's
default/devnet ELF mismatch (D191) stands and is pv-rebase's job. The worker stopped with 62 Lean
attempts unused, against the completion rule. pv-dict6 relaunches on the same branch with a
changed task: prove by reachability over the extracted erased caller which of the 99 operations
and 2 types the refinement actually requires, then take the reachable error-carrier/IO entries by
the P6 owned-reference route. Privacy target not yet established.

## D194 (Stream B, 2026-10-26 09:55): three early returns reviewed; launcher range extended; three relaunches

pv-rebase (head 3f9177b647) merged research into the candidate without conflicts and stopped at the
source-identity condition: four aspis-core files differ (Cargo.toml feature `ct-host-prover`,
field.rs, field/ct.rs, field/wide_exact.rs). Lead review: every difference is a
`#[cfg(not(feature = "ct-host-prover"))]` guard or feature-gated addition, and the feature is
host-only. The adoption condition is ELF byte identity, not source identity, so pv-rebase2 now runs
the gates in order: three ELFs against the pins with a research control build in the same session,
fixture bytes, the 1000-pair differential, quiet-host timing (<15 s, <=1.10x research). A byte
difference stops the gates and isolates the responsible hunk; no repin is proposed by workers.

pv-client (head 149855299b, merged into research d13ac3cb43; docs and an audit tool only):
the operational R1 runner (`devnet_spend`, planner plan.rs:112) still calls the Generic96 route;
`RealR1_client::prove_for_proof_accounts` (proof-account route, D162) is unwired; the release ledger
pins no client. The minimal change needs tools/ and scripts/ only. D162 decision 1 already
authorises this client change, so pv-client2 wires the runner to the proof-account route, makes the
96-byte route unreachable with a test, and produces the acceptance receipt against the pinned ELFs
plus source pins. No crates/ or programs/ change is permitted; one would stop the job.

pv-l2-sim (head 5048eb9408, merged dd6bb7ee09; design note and row report only, all rows open)
was refused by the shared launcher: `attempt 20100 outside 5000-9999`. Lead fix on the host,
range only: run-joint.sh line 20 now also accepts `2[0-9][0-9][0-9][0-9]`; backup
`run-joint.sh.bak-streamB-20261026`; new sha256 9804d43be78c1b83343d5c0545bd2cd4da0bb413a92ad202b5604210b9cbb864;
probe 20100 passes the range check, 30000 is refused. The launcher's TasksMax=128 is its standing
setting and is accepted for run-joint.sh compiles (memory caps unchanged). pv-l2-sim2 relaunched
with its full budget. Six jobs running. Privacy target not yet established; no premise removed.

## D195 (Stream B, 2026-10-26 10:40): privacy premise ledger merged; baseline counts; RunJoin job

Merged `codex/pv-ledger-20261026` (b59fa7293a): `design/PRIVACY-LEDGER-20261026.md` with evidence
under `evidence/privacy-ledger-20261026/` (mechanical #check/#print captures J20002/20004/20005,
explicit-binder source block, non-vacuity audit, pins). Audit only; no theorem added; 5 of 15 Lean
invocations used. This is the baseline against which Stream B progress is measured.

| Scope | T | P | C |
|---|---:|---:|---:|
| All syntactic rows (399) | 26 | 369 | 4 |
| Remaining obligation/trust/vacuity families | 26 | 161 | 4 |

The difference between the two lines is data/guard fields (42), already-proved internal families (87),
carried honest-domain guards (22) and explicit native-cut overlaps (57), listed separately so they are
not counted as open gates. Owners: stream B 373, external 26. The `Admitted` namespace in the proof
is not a Lean admission; its hidden model facts are inventoried. Highest-fan-out blocker: V038, the
concrete deployed `RunJoin.agreement` (complete view and observer decision equal to the model outside
the fixed bad event), with its two marginal laws V036/V037 on the same coupling. C rows: V045 the
deployed `rust` instance is a free parameter with no deployed-prover certificate; V046 adversary
inhabitance; V047 matching witness/public fibre for arbitrary x; V270 the Formatter axiom route
(forbidden, unselected). The ledger notes the LOG numbering collision without editing the LOG.

New job pv-runjoin (`codex/pv-runjoin-20261026`, branched from the candidate, prefix PV_RunJoin_,
IDs 20900-21199): define the deployed FSExperiments instance from the candidate's extracted
proof-account prover with an explicit entropy world as RealRand, prove non-vacuity for the two release
fixtures, build the coupling with both marginals, and reduce `agreement` to a named premise structure
with one field per ledger row. Six jobs running. Privacy target not yet established; rows removed: 0.

## D196 (Stream B, 2026-10-26 11:20): operational client wired to the proof-account route (D162); L3 job

Merged `codex/pv-client-20261026` into research. This implements the owner's D162 decision 1: the
operational R1 runner (`tools/r1-cost-probe/src/bin/devnet_spend`, planner `plan.rs`, account helper
`Client64_accounts.rs`, and the `scripts/` retention/inventory/driver helpers) now calls
`RealR1_client::prove_for_proof_accounts`; publication is bound to the successful retained key; a
regression test excludes the Generic96 fallback. No file under `crates/` or `programs/` changed
(`git diff --stat research.. -- crates programs` empty), so the release pins are untouched.
Validation: 31 Python tests and three optimized Rust tests; transfer and withdrawal proofs produced
through the wired route are accepted by both pinned verifier ELFs and the pinned Pool in four signed
LiteSVM cases; duplicate nonces return `Semantic` and leave the durable ledgers unchanged. Integration
run: exit 0, 195.957 s, 547,352 KiB peak RSS, swap 0 (`evidence/pv-client-20261026/runtime-02-public/
acceptance.json`); 1,295 source pins and the exact entry/call chain in `client-pins.json`. Process
deviation recorded by the worker: one barrier retry after 110.6 s instead of 180 s; the retry passed
admission independently. Reversible by reverting the merge if the owner objects. What this closes:
the operational routing mismatch found in D194. What it does not: the release ledger still pins no
client bundle (a soundness-stream file; recommendation to the owner: pin `client-pins.json`), and
`RustRealRefinement`, E1/E2, RunJoin and L1/L2/L3 stay open. Ledger rows removed: 0 until recount.

New job pv-l3 (`codex/pv-l3-20261026`, branched from the merged candidate, prefix PV_L3_, IDs
21200-21299): V372 platform pins, V373 disassembly audit of the CT kernels and witness-bearing call
sites, V374 dudect-style two-class measurement with pre-registered criteria, and the exact statements
of the V370/V371 trust items for owner acceptance. All labelled measurement, never proof. Six jobs
running. Privacy target not yet established.

## D197 (Stream B, 2026-10-26 12:30): rebase gates passing; L3 partial audit with two escalations; rw15 and L1 jobs

pv-rebase2 (branch `codex/pv-rebase-20261026`, unmerged candidate + research): all three ELFs built
from the merged revision 3f9177b647 hash exactly to the release pins (default f8c0ec72…, 1,563,728 B;
devnet 63ad3e9c…, 1,563,728 B; Pool 121f3e29…, 605,704 B), and a research control build in the same
session reproduces the same three. Fixed-coin transfer and withdrawal proofs are byte-identical to
research (proof 57,607 B, public 1,455 B; equal status/callbacks/attempts/audit). Lead ruling: the
host-only `ct-host-prover` feature guards in aspis-core are admitted for adoption, since verifier bytes
are unchanged. The D191 ELF divergence came from the missing research adoptions, not the CT kernels.
Ledger rows V341–V343 now have passing evidence (not yet recounted). The 1000-pair differential and
the quiet-host timing gate are still running. No binaries committed.

pv-l3 (branch `codex/pv-l3-20261026`, from the merged candidate; report design/PV-L3-20261026.md):
V372 platform pins recorded (optimized native prover executable, rustc/LLVM/flags, Intel Core Ultra 7
155H, microcode, kernel). V373 disassembly audit PARTIAL over 52 kernel entries: M31/CM31/QM31/
WideExact CT leaves compile to CMOV/SETcc/SSE masks with no secret branch or index; two STOPs retained:
(a) the pole-verdict caller branches on the scan verdict (`je` at 0xa739d) to select ActivePole; this
is the already-modelled L1 retry boundary (P_R1 rejection), not a new arithmetic leak; (b) the
inversion-validity branches (`try_inv` on M31/QM31/WideExact) test for zero, so constant time is
certified only on the nonzero domain. V374 timing: zero samples, the host load was about 20 with
three other scopes; a guarded collector waits for a quiet host and will commit evidence locally on
that branch. Read-only MSR snapshot: CPU0 supports DOITM (data-operand-independent timing mode) but it
is DISABLED (IA32_UARCH_MISC_CTL = 0). All L3 results are measurement/trust, not proof.

**Escalations to the owner (recommendation in each):**
1. V371 CPU-latency trust item. With DOITM disabled, branchless code alone does not give
   data-independent latency on this CPU. Recommendation: enable DOITM on the pinned build/prover host
   (kernel/MSR setting, recorded as a platform pin) before the L3 measurement run, and accept V371
   only for the DOITM-enabled mode; otherwise V371 stays a substantive trust item.
2. Inversion zero-boundary. Recommendation: have the L2 job prove that every `try_inv` operand on a
   witness-bearing path is nonzero except on an already-charged bad event (so the branch is
   simulatable); if a witness-dependent zero is reachable, that is a protocol-level leak for decision.

prover-rw14 stopped on the same launcher ID quirk as dict6 (barrier refusal then "attempt 14835
already used"); it had supplied two callbacks (33 remain), 35/100 Lean and 3/15 Kani used.
Relaunched as pv-rw15 (IDs 21300–21599, remaining budget) on the proof/audit data equality,
compression correspondence and callbacks. New job pv-l1 (`codex/pv-l1-20261026`, from the merged
candidate, prefix PV_L1_, IDs 21600–21899): V347–V351 native L1 event producer and joint law, plus
V366 on the same coupling. Six jobs running. Privacy target not yet established; rows removed: 0.

## D198 (Stream B, 2026-10-26 13:10): L2 stage 2 merged; all F3/F5/F6 rows still open; l2-sim3

Merged `codex/pv-l2-sim-20261026` (9f7205e539; research-based, no crates/programs change, no forbidden
tokens). pv-l2-sim2 used 100/100 Lean (45 successes, 140 declarations audited standard-only) and
20/20 Kani (11 pass, 8 timeouts, 1 unwind failure). Proved: actual QueryScan raw history transport to
lazy and completed tapes (`Headline.real_to_lazy_actual`), fixed-coin absorption to the unchanged
simE (`Headline.absorption_actual`, `HeadlineF3.absorption_actual`), owned-source entropy/masking
count absorption (`F3SourceBudget`, `F3Tape.owned_joint_law`), and extracted checker erasures
(`F6Dot/KDot/Image/Pivot/Product`). The generic local hypotheses (RAddrIn, RCausal, PublicBase,
BuilderSoundOn, capacity budgets, conditional fibres) were discharged for the actual domains; no new
endpoint assumption. Every complete F3/F5/F6 row (V352–V365) remains OPEN: the proved pieces are
model/parser transports and sub-steps, not the whole native-trace law. `F3SeedObstruction.
lifted_position_changes` (J20118) is a checked counterexample to a proof inference (successful-seed
permutation does not preserve the first-nonzero position), not a witness attack; the replacement
construction fixes the raw E1 tape. Rows removed: 0. pv-l2-sim3 continues with a fresh budget on the
E1/expander record joined to the full L1 attempt record and ROM history, the new inversion
zero-boundary row V380 from D197, then the F5/F6 rows, reporting CLOSED/REDUCED/OPEN per row.

## D199 (Stream B, 2026-10-26 14:30): host barrier cause; disk-full interruption; runjoin and dict rounds

Host barrier. Stream A reported refusals "projected reservations above 55 GiB" at about 11 GiB actual
use. Cause (lead, read from run2.sh/run2-par.sh/run-joint.sh on the host): the projection is the live
sum of memory.max over every populated cgroup scope, and eight Docker container scopes under
system.slice carry finite caps of about 23 GiB while using about 8 GiB. With two 8 GiB run scopes the
sum is 40 GiB; a third makes 56 and holds. So the host admits three capped Lean/Rust scopes at a time
across both streams regardless of job counts. No stale records exist; no launcher logic was changed.
Owner decision requested (recommendation: shrink the Docker caps to their real profile; alternatives:
exclude Docker from the projection, or accept the three-scope ceiling). Stream A concurs.

Disk. The Mac root volume filled at 10:51 UTC (23 worktrees, 122 GB under .worktrees); pv-rw15,
pv-runjoin and pv-l1 died with "No space left on device" and their output files never finalised. The
lead committed WIP snapshots in the three worktrees and relaunched them with resume preambles
(rw16, runjoin2, l1b). Merged Stream B worktrees are removed on merge; the remaining 16 non-Stream-B
worktrees are Stream A's and session A's.

pv-runjoin2 (`codex/pv-runjoin-20261026`, head 55749bbc7f, 50/100 Lean, 0/10 Kani): shared coupling
from explicit model coordinates; complete-observer agreement characterised; conditional endpoint
composed; canonical fixture fibres for transfer and withdrawal (V047 discharged for the shipped
statements, fields `transfer_public_V047`/`withdrawal_public_V047`); finite cap8 entropy replay.
Checked counterexample: a native probe observed two distinct successful entropy outputs at one public
nonce, so one pure ExternalFuns dictionary cannot represent both; same obstruction as D190, route
already chosen in D191–D193. Lead ruling: the RunJoin's RealRand is the explicit (tape, cursor,
policy, ledger) world; runjoin3 relaunched on that route with the remaining budget. Fields still open:
`uniform_V037`, `disclosed_V038`, `observerOracle_V038`; V045 instance incomplete.

pv-dict7 (`codex/cx-prover-dict-20261026`, head ea4fd01ba3, 74/74 Lean, 15/15 Kani, audit J20701
exit 0, 6.73 s, 4,331,620 KiB, swap 0, 486 standard-axiom reports): seven-field independence proved
through the actual extracted proof-account caller; thirteen pure entries installed; owned-error
reference extracted with its source observations; sufficient source requirements 172/255 selected,
83 open (255 is a sufficient overapproximation, not yet the exact invocation set); types 26/28.
Crate changes unchanged since D193 (cfg(kani) harnesses only). dict8 relaunched on the fallible-store
transport, full carrier caller lift, and the native error/File-world quotient for types 3 and 27.
Root conjunct-1 premises removed: 0. Six jobs running. Privacy target not yet established.

## D200 (Stream B, 2026-10-26 15:40): L2 stage 3 merged; L2 paused pending native association; recount job

Merged `codex/pv-l2-sim-20261026` stage 3 (8524c4269d; research-based, no crates/programs change).
pv-l2-sim3 used 100/100 Lean and 20/20 Kani (121 theorem results, standard axioms; 17 Kani passes):
full rejected-attempt L1 and ROM prefixes preserved through source attempts; failure-preserving seeded
source transport; whole extracted checker erasure; and, for the D197 inversion escalation, a PARTIAL
result: `PV_L2_InversionQ.logup_operand` proves the extracted QM31 inversion takes the nonzero branch
for every non-pole operand (operand nonzero derived from the model `NoPole` for every active copy row),
with inversion success a conclusion, not a hypothesis. The whole inversion row stays OPEN: native
reached-call enumeration, slot correspondence, and the M31/WideExact/circle/interpolation/certificate
paths still need caller nonzero arguments. No witness-dependent zero was found. Row outcome: 0 CLOSED,
0 REDUCED, 19 OPEN, after two full L2 rounds.

Lead assessment (owner rule: when the must-prove count stops falling, reconsider rather than add
workers): the L2 job's own next deliverable is the native E1 seed-event producer and ordered ROM
association on the headline coupling, which is the same native-refinement work as conjunct 1 /
V038. L2 rows are therefore downstream of the RunJoin and will not close from more trace-erasure
helpers. The L2 slot is paused and reallocated to a mechanical RECOUNT and dependency audit of the
ledger (pv-recount, `codex/pv-recount-20261026`, audit only), which will classify every open row as
independent, downstream of the native refinement, or downstream of an owner decision, and credit the
evidence now on research (ELF identities, fixture fibres, client route). Ledger ID note: the L2
report's "V380 (inversion)" collides with the ledger's existing V380 (TrustedStd
`btree_entry_or_insert_with`); the recount assigns the inversion row a fresh ID. Six jobs running:
rw16, dict8, runjoin3, recount, rebase2, l1b. Privacy target not yet established.

## D201 (Stream B, 2026-10-26 16:30): first privacy recount; dependency buckets; source-identification job

Merged `codex/pv-recount-20261026` (322afc54f7; audit only, 0 Lean, 0 Kani): a dated "Recount
2026-10-26 (B)" section appended to `design/PRIVACY-LEDGER-20261026.md`, per-row audit in
`evidence/privacy-recount-20261026/ROWS.md`, original rows intact. The inversion obligation from D197
is recorded as `V380-inversion` (the ledger's V380 already names TrustedStd `btree_entry_or_insert_with`),
so there are 400 obligations. T/P/C 26/370/4.

| Status | Baseline (normalised) | Recount 1 |
|---|---:|---:|
| OPEN | 167 | 138 |
| REDUCED (to named premise fields) | 145 | 152 |
| EVIDENCED (gate/measurement passed) | 0 | 10 |
| CLOSED on research | 87 | 87 |
| CLOSED on the unmerged candidate | 0 | 13 |

The 29 rows that left OPEN went to REDUCED (7), EVIDENCED (10: the three ELF identities, fixture
bytes, client route rows V392–V395 and others) and CLOSED-ON-CANDIDATE (13, the candidate's proved
callbacks/replays, which count only once the candidate is adopted). No endpoint premise changed.
Dependency audit of the 138 OPEN rows: 79 independent of the native refinement; 51 downstream of the
native interpretation (cannot close before the extracted deployed caller is interpreted, including all
inherited L2 whole rows); 8 downstream of named owner decisions (V370 compiler trust, V371 DOITM,
V373 inversion zero-domain handling, V396 client bundle pin, and related). Most valuable independent
row per the audit: V164 compression correspondence (already pv-rw16's stage 2). The freed slot goes to
the independent rows V152–V154 (`BuilderSource.SourceIdentification`: public_eq, build_eq,
transport_eq), consumed by the headline via `builder_premises`: job pv-srcid (`codex/pv-srcid-20261026`,
prefix PV_Src_, IDs 22550–22799). Six jobs running: rw16, dict8, runjoin3, srcid, rebase2, l1b.
Privacy target not yet established.

## D202 (Stream B, 2026-10-26 17:20): L1 paused on the shared native obstruction; independent callback job

pv-l1b (`codex/pv-l1-20261026`, head 6351160ce6, from the merged candidate; 100/100 Lean, 54 passed,
0/15 Kani; audit J21698 exit 0, 2.28 s, 4,291,916 KiB, swap 0, 121 declarations standard-only):
ordered source attempt/count correspondence, retry-origin and failure prefixes, conditional joint
source/raw-input transport, contiguous RNG ordinals, and the exact seventeen-digest eager-query abort
prefix. Rows V347–V351 and V366: open → open; `PV_L1_Premises` holds one unproved field per row.
Its next deliverable is "the complete native callback producer for the operational proof-account
client", i.e. the same native interpretation that L2 (D200) and RunJoin (D199) wait on. Per AGENTS.md
§7 (investigate a shared obstruction rather than commission more wrappers) the L1 slot is paused;
the branch is kept as an unmerged sibling of the candidate and its worktree removed for disk.

The three paused/converging tracks (L1, L2, RunJoin) all need the effect-aware interpretation of the
extracted deployed caller; pv-runjoin3 carries that route (D199 ruling), with pv-rw16 and pv-dict8
supplying the callbacks and dictionary it consumes. The freed slot goes to the recount's largest
independent bucket, the ~70 selected-callback rows V169–V267 (`ProverRwFull.ExternalFuns.opN`),
as pv-cb (`codex/pv-cb-20261026`, from the candidate, prefix PV_CB_, IDs 22800–23099), ascending
op order, skipping ops a sibling installs first and deferring effectful ops to the RunJoin route.
Six jobs running: rw16, dict8, runjoin3, srcid, rebase2, cb. Mac disk: 24 GiB free. Privacy target
not yet established.

## D203 (Stream B, 2026-10-26 18:10): dict8 reviewed; dictionary refocused away from the shared lift

pv-dict8 (`codex/cx-prover-dict-20261026`, head 4cd294bc60; 100/100 Lean, 53 passed, 47 rejected;
0/15 Kani; audit 433 standard-only reports, 3.98 s, 4,326,772 KiB, swap 0): fallible nonce-store and
reserve/material state transport proved without the former fallible-run hypothesis; public-carrier
transport through the semantic and masked proof bodies; V269 reduced; V263 (`WorkExtensional`,
op257) still an explicit contract; V268/V269/V271 native Error/Formatter/File-world open. Counts
unchanged: 172 selected / 83 open / 255 sufficient requirements; types 26/28. Root premises removed: 0.
The stage it spent the budget on, the full store/retry/client lift, is the same shared native
interpretation obstruction as L1/L2/RunJoin (D199, D200, D202), now owned by pv-runjoin3. dict9 is
relaunched refocused on what moves counts: types 3 and 27 by the Kani-first quotient route (15 unused
runs), the open pure entries outside pv-cb's op list, and the V270 Formatter quotient. Six jobs
running: rw16, dict9, runjoin3, srcid, rebase2, cb. Privacy target not yet established.

## D204 (Stream B, 2026-10-26 19:00): deployed endpoint reduced to an 8-field premise record

pv-runjoin3 (`codex/pv-runjoin-20261026`, head 92a6c256a6, unmerged sibling of the candidate; 50/50
Lean, 31 passed; 10/10 Kani, 8 passing harnesses; axioms audit standard-only; swaps 0) delivered the
structure Stream B is measured against: `PV_RunJoin_Endpoint.privacy_headline_from_premises :
PV_RunJoin_Premises → <the exact conclusion of privacy_headline_deployed at the deployed rust>`, with
the original conclusion, public-equality guard, bad event, simulator simE and complete observer
preserved, and axioms exactly propext, Classical.choice, Quot.sound. The deployed instance is the
shared-world retry interpretation of the selected client retry owner (explicit entropy tape/cursor,
policy and ledger state), retaining the full native audit; both coupling marginals are proved on one
coupling, so `uniform_V037` is now a theorem for the interpreted world; the concrete fixture fibres
need no assumption (2→0). The record `PV_RunJoin_Premises` has 8 fields / 12 conjunct families:
`source_V045`, `E1_V329` (trust item, stated exactly), `native_fill_V336`, `native_ledger_V337`,
`byte_blind_V338`, `kernels_V339`, `disclosed_V038`, `observerOracle_V038`. The field count rose
3→8 because the abstract premise was unfolded into its native obligations; that is exposure, not
reduction, and whole deployed rows removed is still 0. Lead review pending on the exact statements
(no forbidden tokens; no crates/programs change). pv-runjoin4 relaunched with a fresh budget to
discharge the fields in order of least native dependence (kernels, byte-blind, ledger/fill, then
source/V038 by composing pv-rw16/pv-cb/pv-dict9 results as they land), splitting any remainder into
finer named fields so the record tracks the ledger. Six jobs running. Privacy target not yet established.

## D205 (Stream B, 2026-10-26 19:20): correction to D204 after reading the endpoint statement

Lead review of `PV_RunJoin_Endpoint.lean` (head 92a6c256a6) corrects D204. The endpoint theorem
keeps the exact conclusion and standard axioms, but it is still PARAMETRIC: it quantifies over a free
`runtime : PV_RunJoin_Deployed.Runtime …` and `boundary : PV_RunJoin_Boundary.Data runtime …`, and
`rust := PV_RunJoin_Deployed.rust runtime`. So D204's sentence "the deployed instance is the
shared-world retry interpretation of the selected client retry owner" is superseded: the interpretation
is defined for an abstract runtime record, and the instance for the frozen extracted client has not
been constructed. V045 (deployed rust instance) therefore remains open, and the `source_V045` field
is a law relating `boundary.sourceBody` to `runtime.body`, both still parameters. The two V038 fields
are the agreement split through `complete_view_ext` (view equality ⇒ decision equality), which is
organisation of the premise, not discharge (AGENTS.md §3). What stands from D204: the coupling and
both marginals on the abstract world (`uniform_V037` as a theorem), the fixture fibres, the exact
statement of the eight obligations. Rows removed: 0. pv-runjoin4 was stopped seconds after launch and
relaunched as pv-runjoin4b with the order corrected: instantiate `runtime`/`boundary` from the frozen
extracted operational client first (free parameters 2→0, record restated at the concrete instance),
then discharge fields. This entry is the record of the correction; nothing in the proof tree changed.

## D206 (Stream B, 2026-10-26 20:10): OS entropy failure is outside the model; owner decision requested

pv-runjoin4b (`codex/pv-runjoin-20261026`, head 5090b732a0; 11/100 Lean, 0/15 Kani, stopped early
against the completion rule; audit 23416 exit 0, 25.16 s, 3.18 GB, swap 0; standard axioms) did not
construct the concrete instance (parameters 2→2, fields 8→8, rows removed 0) but surfaced a model gap:
- Proved: the emitted Draw64 owner transports partial-write OS errors and the shared-world client
  stops before the body; normalised kernels satisfy the conditional E1 law with zero success
  availability (E1 does not exclude the fault path, by design: D147 states E1 "without assuming
  availability"); every successful model `firstGood` branch has a nonempty oracle log, preserved by
  reencoding for complete observers; hence an empty native log disagrees with that model-success log.
- Measured: the literal selected entropy factory (pinned getrandom/zeroize) returns `Os(EIO)` under a
  process-only seccomp EIO fault; the EPERM probe did not reproduce because getrandom falls back to
  /dev/urandom (retained as a setup failure).
So a real run in which the OS entropy source fails yields a view (empty log, error) that the current
model never produces, and that world is outside the fixed bad event. This is not a witness-dependent
leak claim: no outside-bad witness/decoder counterexample is constructed yet, and OS failure is
expected to be witness-independent (to be proved by runjoin5).

**Escalation 3 to the owner (contract/model, D185 comparison contract).** Two repairs, neither adopted:
(A) availability-conditioned endpoint: add a named environment assumption `OsAvailable` (getrandom
does not fail during the proof-account run) as a trust item; the headline statement is otherwise
unchanged. (B) failure-as-public-input: make the environment failure signal a public input to BOTH
experiments so the simulator sees the same witness-independent failure; the error bound is unchanged,
but the model statement changes. Lead recommendation: (B), because it needs no new trust and keeps
the observer complete (an attacker who can induce EIO sees the failure in both worlds), provided
runjoin5 proves the failure event witness-independent; (A) otherwise. pv-runjoin5 relaunched with the
remaining 89 Lean / 15 Kani to state the disagreement exactly, prepare both options as separate stated
theorems, and continue the concrete instance. Six jobs running. Privacy target not yet established.

## D207 (Stream B, 2026-10-26 20:40): rw16 done, two callback rows supplied; rw17 on compression by split steps

pv-rw16 (`codex/cx-prover-rw-20261023`, head 5d97a425c5; 65/65 Lean, 48 passes, standard axioms;
12/12 Kani: nine timeouts, three driver/compiler/check failures; focused audit over 1,224 cached
dependency hashes): callbacks V262/op255 and V255/op247 supplied through the complete caller
(33 → 31 remain); current complex/quartic arithmetic transports, owned compression structure, symbolic
pole/polynomial bounds and the indexed ordinary-reference policy proved. V163 (whole proof/audit data
equality) and V164 (shipped arity-16 compression correspondence) stay OPEN: the Kani harnesses over the
shipped compression and sampler loops time out. Root premises removed: 0; two ledger callback rows
move to CLOSED-ON-CANDIDATE at the next recount. pv-rw17 relaunched with a fresh budget and a ruling:
no unchanged reruns; V164 by the P6 route decomposed per step (owned reference, per-step Kani with a
proved-sufficient bound, Lean induction over steps, the route that worked for parts 47-48), then V163,
then callbacks outside pv-cb's list. Six jobs running: rw17, dict9, runjoin5, srcid, rebase2, cb.
Privacy target not yet established.

## D208 (Stream B, 2026-10-26 16:05): cb done, 30 value interpretations but 0 rows discharged; cb2 converts them to source equations

pv-cb (`codex/pv-cb-20261026`, head c0e2f7af57, branched from the unmerged candidate; 100/100 Lean,
20/20 Kani: 13 passes, 5 timeouts, 2 unwinding failures; final audit receipt 22900.json exit 0,
peak RSS 4.3 GiB, standard axioms): 30 callback ops received a checked "selected dictionary equation"
(PV_CB_* value interpretations), 7 reused sibling installations, 5 ops deferred to the effect-aware
route (zeroize volatile writes/fences ops 122/123, Instant timing op 232, worker pool op 257), 31 ops
open; symbolic owned encoder/mask totality and the exponent-table widening proved for op117. No
shipped crate or program file changed. Lead review: a dictionary equation is organisation, not the
row's law; rows V169-V267 require the entry to equal the shipped function's source semantics
(extraction, D188, or the P6 reference), so 73 rows before → 73 after, 0 removed, and the review's
"native correspondence remains open" notes are irrelevant to pure ops (that composition is V165/V167,
owned by RunJoin). The branch is a sibling of the candidate and will be merged into
`codex/cx-prover-rw-20261023` when rw17 releases that worktree (not into research). pv-cb2 relaunched
in the same worktree (IDs 24000-24299, 100 Lean/20 Kani): stage 1 converts the 30 installed pure ops
to proved source equations against the extracted definitions, stage 2 the 25 open pure laws, stage 3
op117 by per-step P6 with Lean induction. Six jobs running: rw17, dict9, runjoin5, srcid, rebase2,
cb2. Rows removed outright: 0. Privacy target not yet established.

## D209 (Stream B, 2026-10-26 16:40): rebase2 passes ELF, fixture and differential gates; timing blocked on a quiet host; recount 2 launched

pv-rebase2 (`codex/pv-rebase-20261026`, head dacdb225ff = candidate with research merged; Lean 0,
Kani 0; no binaries committed): all three ELFs rebuilt from the merged candidate hash exactly to the
release pins, with research rebuilt in the same session as control (default/devnet 1,563,728 B, Pool
605,704 B); the four shared-core differences (host-only `ct-host-prover` guards) are therefore
ADMITTED for adoption on the byte-identity ruling (D197). Transfer and withdrawal fixture proofs are
byte-identical to research (57,607 B each). The existing differential harness passed 1,000/1,000
pairs (600 proofs, 100 rejected-prefix pairs), after an earlier oversubscribed cohort was invalidated
and replaced by a capacity-checked one. Quiet-host timing never qualified: ten boundary checks found
one opening, and another capped job started during the first research sample, which invalidates it
(raw research calls 38.2/40.1 s under contention, not medians; candidate never timed). The timing gate
(candidate median < 15 s and <= 1.10 x research, D168/D169) therefore remains OPEN; the prepared
command is NEXT-TIMING-COMMAND.txt in the branch's evidence dir and needs a continuous quiet window,
which does not occur while both streams run six capped scopes. Lead action: ask Stream A to agree a
scheduled quiet window for timing and the pv-l3 collector (owner may rule). The branch stays unmerged
(candidate adoption rule). No premise removed. Slot refilled with pv-recount2 (`codex/pv-recount2-
20261026` from research, IDs 24300-24349, 15 Lean/0 Kani): recount of all 400 rows against the
evidence on research and the unmerged branches, with the ruling that dictionary installs and bounded
Kani gates are not closures, a new row for the OS-entropy failure (D206), and an explicit check of
the lead's D196-D208 claims against the evidence. Six jobs running: rw17, dict9, runjoin5, srcid,
cb2, recount2. Rows removed outright: 0. Privacy target not yet established.

## D210 (Stream B, 2026-10-26 16:55): dict9 three entries (175/255), stopped on a no-stubs question; ruling given, dict10 launched; quiet window agreed

pv-dict9 (`codex/cx-prover-dict-20261026`, head dfd8a438bc; 59/100 Lean, 45 passed; 15/15 Kani: 10
passed, 4 timeouts, 1 unsupported; audit J23158 standard axioms; no crates/programs change): entries
78 (fibre point, V200), 231 (trace clone, V248) and 247 (CT trace value, V255) installed in
`R1Z.PDict_RemainingDictionary231` (172 → 175 of 255 selected; 83 → 80 open; types still 26/28), plus
`client_independent` (replacing these raw callbacks leaves the proof-account caller unchanged at the
selected dictionary). It stopped with 41 attempts unused asking whether "no stubs" permits an explicit
nondeterministic C ABI environment, because Kani rejects actual File::open at the foreign `open64`.
Lead ruling (D210): no; a C ABI replacement is a stub, and Kani's reach ends at the OS boundary. The
OS-call outcomes are a world interface for the effect-aware route (D190-D193, PV_RunJoin_World /
CallerWorld / E1Tape): Kani only for pure projections, the File/OS paths by Lean against extraction
with outcomes read from the world state, and each OS-outcome law surfaced as a named world field
(never an axiom) for matching against runjoin5 and E1/E2. Entry 255 (`from_fn`, Aeneas mutable-borrow
copy rejection in core) goes by the P6 route or a hand-stated monomorphic extraction with its identity
obligation recorded; no backend patch. pv-dict10 relaunched with 81 Lean / 10 Kani (IDs 24400-24699).
Host scheduling: Stream A and Stream B agreed a quiet window 16:50-17:20 UTC (marker
/home/dombarker/project-offloads/QUIET_WINDOW.json; both streams' launchers refuse while it is in
force; LEAD RULING (e) for Stream B workers) for the prover timing gate (D209); the shared launcher
run-joint.sh gained the hold check before any attempt ID is consumed (backup
run-joint.sh.bak-quietwin-20261026). Six jobs running: rw17, dict10, runjoin5, srcid, cb2, recount2.
Rows removed outright: 0. Privacy target not yet established.

## D211 (Stream B, 2026-10-26 17:00): recount 2 merged: 27 rows to CLOSED-ON-CANDIDATE, four lead corrections; cb3 launched

pv-recount2 (`codex/pv-recount2-20261026`, merged into research; 15/15 Lean statement checks, 0 Kani;
only design/PRIVACY-LEDGER-20261026.md and evidence/privacy-recount-20261026/ touched): 403 rows
(26 T / 372 P / 5 C) after adding V400 (OS-entropy failure coverage, D206), V401 (fixture byte
equality) and V402 (differential corpus). Status totals, recount 1 → recount 2: OPEN 138 → 110,
REDUCED 152 → 154, EVIDENCED 10 → 12, CLOSED-ON-RESEARCH 87 → 87, CLOSED-ON-CANDIDATE 13 → 40.
The 27 new candidate closures are complete extracted source equations under D188: 24 PV_CB_Op*Source
theorems already produced by pv-cb2 (V169, V197-V199, V202-V206, V208-V216, V218, V223, V224, V226,
V227), dict9's op78/op231 (V200, V248) and rw16's op247/coefficients (V255, V262); native composition
stays V165-V167. OPEN buckets: independent 79 → 51, downstream of the native interpretation 51 → 50,
owner decisions 8 → 9 (the OS-failure repair added). Corrections to the lead's LOG, recorded plainly:
D199 overstated V047's fibre closure; D201's "29" should read 30; D203 does not support reducing the
whole Formatter row V269; D206's disagreement theorem is conditional (D204 was already corrected by
D205). The endpoint record (D204/D205) keeps runtime/boundary 2 → 2 and fields 8 → 8: REDUCED, not
discharged. Endpoint premises removed: 0. The 51 independent OPEN rows are all owned by running jobs
(callbacks: cb2; V152-V154: srcid; V163/V164: rw17), so the freed slot runs pv-cb3
(`codex/pv-cb3-20261026` from the candidate, prefix PV_CB3_, IDs 24700-24999, 100 Lean/20 Kani) on
the stage-2 callback rows from the top down (ops 258, 253-251, 230-205) while cb2 works upward.
Six jobs running: rw17, dict10, runjoin5, srcid, cb2, cb3. Privacy target not yet established.

## D212 (Stream B, 2026-10-26 17:05): first quiet window broken after one sample; second window requested

The 16:50-17:20 UTC quiet window (D210) opened on time: the marker was written at 16:50:00, the strict
preflight found the host quiet at 16:50:40, and the timing driver started in one 6G/8G/no-swap/64-task
scope. The first research sample completed (transfer 48.5 s, withdrawal 46.4 s, 16 workers, load 2.5;
proof hashes as pinned), but the post-sample preflight found a new capped scope from Stream A's
`codex-cx-sound-int2-20261025/S2W_run_host.py` (a launcher outside the S2X_/S2H_ reservation scripts
Stream A had patched), refused with exit 78, and the driver stopped by design (receipt
candidate/quiet-timing-2/receipt on the host; exit 1, 95 s, peak RSS 0.57 GiB). The marker was removed
at 16:52:15 so Stream A lost about two minutes. The sample is UNQUALIFIED and no timing number is
claimed; for context only, D172 measured the CT-kernels-v2 candidate at 13.6/14.0 s medians against
about 37-39 s before it, and research has not adopted that candidate, so a large candidate/research
ratio below 1 is expected rather than a regression signal. Stream A has been asked to patch the
remaining launcher(s) and name a second 30-minute window from 17:40 UTC; the orchestration script will
be re-pointed at the new epoch with the same early-release rule. Six jobs running: rw17, dict10,
runjoin5, srcid, cb2, cb3. Privacy target not yet established.

## D213 (Stream B, 2026-10-26 17:10): srcid merged, V152-V154 reduced to five source premise families; srcid2 launched

pv-srcid (`codex/pv-srcid-20261026`, merged into research; 100/100 Lean, 15/15 Kani; final audit 22689
standard axioms; no crates/programs change): `R1Z.PV_Src_NativeIdentification` proves `public_eq`,
`build_eq` and `transport_eq` (V152-V154) for successful returns of the extracted forest compiler and
constructs the original `SourceIdentification` certificate, which the unchanged `BuilderPremises`
consumer accepts (receipt 22677). The three rows are REDUCED, not closed: five `PV_Src_Premises`
families remain (compile_call, words, publicCorr, admission, row_call) with their nested obligations
explicit; both canonical fixture fibres are inhabited through the extracted bank/column stages; full
native fixture inhabitance, callee association and deployed installation stay open. Kani: 11 of 15
runs were charged to misnamed harnesses that exited before verification (worker's own report); ruling
for successors: list harness names before charging, stop the queue on the first configuration
failure. No endpoint premise removed. pv-srcid2 launched from research (IDs 25000-25299, 100 Lean/15
Kani) to classify each family as pure-source or native-association and discharge the pure ones for
both fixtures. Six jobs running: rw17, dict10, runjoin5, srcid2, cb2, cb3. Second quiet window
17:45-18:15 UTC agreed (Stream A's systemd-run shim covers every bare launch; owner bypass for the
timing driver). Privacy target not yet established.

## D214 (Stream B, 2026-10-26 17:50): srcid2 stopped on a source-domain fact that is not a row counterexample; ruling, srcid3 launched

pv-srcid2 (`codex/pv-srcid2-20261026`, merged into research; 4/100 Lean, 11 Kani invocations with two
timeouts and one configuration waste, no completed verification; standard axioms; no crates/programs
change; one appended cfg(kani) diagnostic harness in tools/r1-builder-reference/records.rs): the five
`PV_Src_Premises` families stay 5 → 5. publicCorr is REDUCED to the exact seven-field PubCorr of the
returned record, admission to RspendPlus on the selected record, row_call to the installed-transport
equality; compile_call and words stay OPEN. The worker stopped on a "checked source counterexample":
an optimized native diagnostic importing the exact mapper, pair_trace, poseidon2 and spend files with
no stubs shows CopyRecords::new and banks succeed with merged[10][1010] = 2^30, outside WitnessOk's
range. Lead ruling (D214): that refutes only the UNCONDITIONAL raw-mapper lemma the worker chose; the
ledger rows V152-V154 and the words family are statements about the selected inputs of the deployed
caller, so words is REDUCED to `PV_Src_RecordReference.Checked` on those inputs and the condition is
to be discharged from the deployed input validation (client route D162 and/or canonical admission),
not treated as a stop. The counterexample harness is retained as evidence (AGENTS §7). pv-srcid3
launched from research with the unused 96 + 4 Lean and 12 Kani (IDs 25300-25599): discharge Checked
for both fixtures and the canonical instance, then words by unstubbed P6 equality, then publicCorr's
pure sub-obligations and compile_call's pure callees. No endpoint premise removed. Six jobs running:
rw17, dict10, runjoin5, srcid3, cb2, cb3. Quiet window 2 (17:45-18:15 UTC) in progress. Privacy
target not yet established.

## D215 (Stream B, 2026-10-26 17:55): runjoin5 done: OS-failure theorem and both repairs stated, endpoint record unchanged; runjoin6 on the residual fields and the concrete instance

pv-runjoin5 (`codex/pv-runjoin-20261026`, head 4148e0e59c, a sibling of the unmerged candidate so it
stays unmerged into research; 89/89 Lean, final audit exit 0, 33.6 s, peak RSS 2.8 GiB, standard
axioms; 3/15 Kani: one pass, two unsupported `dlsym`; frozen implementation and original endpoint
unchanged): `PV_RunJoin_OsFailure` proves that with a successful first account callback, a nonzero
nonce and a first entropy draw returning Err, execution stops with Entropy independently of the
witness; absent the parser, seed-guess and fuel events this world lies outside the unchanged `bad`,
and with an empty decoded error log against a successful model firstGood branch the complete views
differ (hypotheses explicit; no concrete native outside-bad world constructed). Option A
(`privacy_headline_from_premises_available`, named OsAvailable: every in-capacity draw succeeds) keeps
the exact conclusion and all eight premises; option B (both experiments receive the same public
failure signal) keeps the bound, including under a common finite public-signal distribution, and
changes the model statement. Both remain unadopted pending the owner (recommendation B, D206).
Endpoint accounting: native parameters 2 → 2, fields 8 → 8, rows removed 0; the partial source
constructor has seven data inputs and six residual proof fields. Two procedural violations recorded by
the worker (an attempt launched after an admission refusal; one evidence transfer without a fresh
receipt); the final archive transfer was refused by the quiet window and is retained locally.
pv-runjoin6 relaunched in the same worktree (IDs 25600-25899, 100 Lean, 12 Kani): discharge the pure
residual fields and name the native ones as world fields aligned with dict10, instantiate the concrete
Runtime/Boundary for the proof-account caller, then publish the installed inputs/transport interface
for srcid3 and say which paused L1/L2 rows become dischargeable. Six jobs running: rw17, dict10,
runjoin6, srcid3, cb2, cb3. Quiet window 2 in progress (driver started 17:45:00 with the host quiet).
Privacy target not yet established.

## D216 (Stream B, 2026-10-26 18:00): prover timing gate PASSED in quiet window 2; all four candidate equivalence/performance gates now pass

Quiet window 2 (17:45-18:15 UTC, D213) worked: the host was quiet at 17:45:00, the unchanged driver
ran research first then candidate, five fresh processes per source with coins 100-104 and a strict
quiet preflight before and after every sample (all twenty quiet), and finished at 17:53:44 (exit 0,
524 s, peak RSS 0.65 GiB, swaps 0); the marker was released immediately so Stream A lost under nine
minutes. Medians: transfer research 38.909 s vs candidate 13.742 s (ratio 0.353); withdrawal research
38.560 s vs candidate 13.499 s (ratio 0.350); both candidate medians under 15 s and under 1.10 x
research (D168/D169). Research samples spanned 37.76-39.67 s, candidate 13.04-14.18 s. All ten
public/proof byte pairs identical (proof 57,607 B). Scope: fixture medians on the pinned host only; no
universal cost or side-channel theorem. Recorded on `codex/pv-rebase-20261026` (commit b7f1f3c470:
design/PV-REBASE-20261026.md "Timing gate result", gate-status.json `quiet_timing`, evidence
quiet-timing-3/ and the invalidated window-1 attempt). Candidate adoption gates now: ELF pins PASSED,
fixture bytes PASSED, 1,000-pair differential PASSED, timing PASSED, client route merged (D196). Still
required before adoption, and the reason the candidate stays unmerged: conjunct 1 (real-prover
refinement / V038 RunJoin), E1/E2, the L2 simulatable-trace rows (paused on the same native
interpretation) and the L3 receipt. Ledger effect at the next recount: the timing rows move to
EVIDENCED. Six jobs running: rw17, dict10, runjoin6, srcid3, cb2, cb3. Privacy target not yet
established.

## D217 (Stream B, 2026-10-26 18:20): rw17 done: compression loop equals the owned reference, helper association still open; rw18 launched

pv-rw17 (`codex/cx-prover-rw-20261023`, head c4eb7e74cb; 100/100 Lean, 73 passes; 20/20 Kani, 12
passes, 8 timeouts; final frozen manifest 212 theorem reports plus the unchanged headline audit,
standard axioms, 24.1 s, peak RSS 3.2 GiB, no swap; no production-source or pin change): V164 progressed
to "the composed emitted iterator/arithmetic loop equals the closed owned reference for arbitrary
slices and arity 16, preserving the full Result, accumulator, final power and bounds", consumed through
the auxiliary caller into `BodyData.refinement_of_data` with an exact proof-byte/audit split criterion
(V163). Still open: the association of the emitted combined-transition loop with the ORIGINAL whole
Rust helper (V164) and the concrete model instance with both data comparisons (V163). Rows removed: 0;
no endpoint premise weakened. pv-rw18 relaunched in the same worktree (IDs 25900-26199, 100 Lean/20
Kani): prove the original helper's for-loop context equals the emitted loop by induction over the
extracted definition (D188), perform the op223 join using pv-cb3's source law (op223/V240 is in cb3's
list; no duplication), then V163's concrete instance for both fixtures. Six jobs running: rw18, dict10,
runjoin6, srcid3, cb2, cb3. Privacy target not yet established.

## D218 (Stream B, 2026-10-26 19:15): dict10 done, counts unchanged, OS world fields named; dict11 refocused on the Formatter axiom blocker

pv-dict10 (`codex/cx-prover-dict-20261026`, head af96787aa3; 81/81 Lean, 57 accepted; 10/10 Kani, 5
passed, 5 timeouts; final audit J24481 standard axioms across 235 reports, 1,304 object hashes
matched; no shipped-source change, no stubs, no backend patch): ordered tape replay, request matching,
safe sink observation frames, owned reference loops and safe reference carriers proved; the OS world
signature now has named contextual law fields open64, read, write, sync and close (their laws unproved,
for pv-runjoin6 to associate; no axiom, no E1/E2 change). Counts unchanged for the third round: 175 of
255 entries selected, 80 open, types 26 of 28; root premises removed 0; native obligations V262, V268,
V269, V271 retained. Per AGENTS §7 the lead stops commissioning dictionary rounds against the same
native obstruction. pv-dict11 relaunched in the same worktree (IDs 26200-26499, 100 Lean/10 Kani) on
one target only: the Formatter release blocker (V269/V270, both treated as OPEN since recount 2 found
D203 unsupported): stage 0 a mechanical #print axioms inventory of every root in the candidate's
privacy closure naming the non-standard axiom and its importing modules; stage 1 elimination by the
avoidance route (chunk 26's publish_compact reduction and retry fixed point as symbolic lemmas, rule
2) or by a proved safe Formatter quotient as type 27; success criterion is mechanical (only propext,
Classical.choice, Quot.sound on every root). Six jobs running: rw18, dict11, runjoin6, srcid3, cb2,
cb3. Privacy target not yet established.

## D219 (Stream B, 2026-10-26 19:55): Formatter axiom blocker clear on the candidate (V269/V270 scoped); host disk full, 39 GiB of caches pruned; pv-adopt launched

pv-dict11 (`codex/cx-prover-dict-20261026`, head 615d347232; 23/100 Lean, 6/10 Kani; stopped under
local-lean rule 5 when the host filesystem hit 100%): stage 0 inventory FORMATTER-CLOSURE.md: the
forbidden axiom is `Aeneas.Std.core.fmt.Formatter` (declared by the backend module Aeneas.Std.Core.Fmt,
729 transitive importers); `#print axioms` over 12,920 declarations in 321 selected family modules
(every PDict_/ProverRw*/PV_CB_/PV_CB3_ declaration reachable from ExternalFuns, the P6 body root, the
28 type-slot projections and the deployed headline; receipts J26201 51 s / 4.4 GiB, J26203) shows ONLY
subsets of {propext, Classical.choice, Quot.sound}; no candidate declaration depends on the axiom, so no
avoidance rewrite is needed (the split avoidance files PDict_FmtPublicationFrame/PDict_FmtRetryComplete
exist but are not imported). V269/V270: CLOSED-ON-CANDIDATE for the release-blocker statement only
("every audited candidate declaration ... has axiom closure contained in the three standard axioms");
native type-27 adequacy is NOT credited and types stay 26/28, entries 175/255. Stage 2 proved complete
Result equality and per-coordinate correctness for the extracted owned coefficient reference; native
coefficient-array association open (three timeouts, one solver failure). Audit scope: focused cached
audit, not the coherent release replay.
Host: the root volume (1.8 TiB) reached 100% (19 MiB free) about 19:40 UTC and both streams' launches
failed. Lead action within Stream B's scope only: removed the finished client job's cargo cache (2.1
GiB), 40 orphaned Kani/CBMC solver temp files in /tmp not open by any process and older than 30 min
(7.3 GiB), and 65 cargo-tagged charon-target/native-target/harness target caches in the finished
codex-cx-prover-commit* and codex-cx-adapter-rw workspaces, none open (30 GiB). Receipts, corpora and
sources untouched; live job directories untouched. With Stream A's own pruning the volume is at 141
GiB free (92%). Owner decision requested: the ~30 GiB of differential corpora under
codex-cx-prover-rw-20261023 (smoke/phase/focused paired runs, corpus-1000-002) and the 6.2 GiB
invalidated corpus under codex-pv-rebase-20261026 are evidence outputs whose receipts are committed;
recommendation: archive off-host or delete the invalidated corpus and the superseded smoke/phase
outputs, keep corpus-1000-002.
Slot: dictionary rounds stop (D218). pv-adopt launched (`codex/pv-adopt-20261026` from the candidate,
git-only on the Mac, no host use): sibling merge dry-runs and name collisions, research drift under
crates/ and programs/ since 3f9177b647 (ELF-pin invalidation per path), the privacy import closure map
naming the sibling modules not yet joined into the headline route, the final replay command plan, and
the owner escalation table for the nine decision rows. Six jobs running: rw18, adopt, runjoin6, srcid3,
cb2, cb3. Privacy target not yet established.

## D220 (Stream B, 2026-10-26 20:10): INCIDENT: shared Lean workspace and launcher deleted during the disk prune; six-round results; runjoin7 and join launched before the loss was known

Incident. While both streams pruned the full host volume (D219), Stream A's pattern-based removal of
workspaces "older than two days" deleted the SHARED env-J Lean infrastructure:
/home/dombarker/project-offloads/aspis-joint-20261019 (sources and compiled objects for every J
compile) and /home/dombarker/project-offloads/r1-privacy-build-integration-20261019 (tools/run-joint.sh,
env/J.json, evidence/sent.txt and every host-side out-/time-/sha- receipt). Neither matched the keep
patterns. Every Lean launch on the host now fails for both streams. pv-cb2 and pv-srcid3 stopped under
local-lean rule 5 ("launcher and source tree vanished"; not budget exhaustion); rw18, cb3, join and
runjoin7 will stop the same way. Receipts copied into the repo evidence directories survive; host
originals do not. Stream A has been asked to stop deleting, list what was removed, and rebuild the
launcher and the joint workspace (their infrastructure; sources from git at the pinned revisions, one
cold R1Z build in a 6G/8G scope, hours). Stream B's prune touched only cargo-tagged caches and solver
temp files (D219) and none of the shared paths. Volume now 631 GiB free. Owner: this is reportable as
a process failure; recommendation: shared infrastructure gets a protected path list before any further
pattern-based cleanup, and the launcher/env files are committed to the repo (tools/) so they are
reproducible.
Results before the loss. pv-cb2 (`codex/pv-cb-20261026`, head 641d98b783; 71/100 Lean, 10/20 Kani):
18 of its 73 callback rows now have complete extracted source equations (PV_CB_Op*Source), up from 0;
op117 partial; op105 correction and the combined dictionary prepared but uncompiled; 29 Lean/10 Kani
unspent. pv-srcid3 (`codex/pv-srcid3-20261026`, head 2311884064; 93/100 Lean, 12/12 Kani, 55 accepted
modules, standard axioms): `Checked` DISCHARGED for both fixture validation carriers and every encoded
canonical instance (the excluded boundary is exactly outputValue < 2^30); words REDUCED to the
unstubbed full-mapper equality plus installed input selection; publicCorr DISCHARGED for the frozen
reference (deployed snapshot/root association remains); compile_call OPEN (ExternalLinear equality
verified, Records pending); admission and row_call REDUCED to runjoin6's published interfaces.
Reference premises 5 → 3, accepted by the unchanged consumer; deployed premises 5 → 5; final audit
preserved as drafts pending the host (branch kept unmerged until it can be audited). pv-runjoin6
(`codex/pv-runjoin-20261026`, head 87a332c140; 100/100 Lean, audit 25699 standard axioms, 1/12 Kani):
full source/header projection, common public reservation, selected dictionary equations, both fixture
source projections and the endpoint's row_call transport equality proved; published
PV_RunJoin_SourceSelectionContract / SelectedAdmission / NativeSelectedInputs / InstalledTransport for
srcid3; named world fields for entropy, open/read/write/sync/close, time, workers; endpoint record still
residuals 6 → 6, runtime/boundary 2 → 2, fields 8 → 8. pv-adopt (`codex/pv-adopt-20261026`, git-only):
sibling merge dry-runs show zero Lean-path conflicts and zero public-name collisions (one conflict in a
historical launcher file); research drift under crates/ and programs/ since 3f9177b647: 0 paths, so the
ELF-pin evidence stands; 990 sibling-family modules are not imported by the headline route (579 live
only on sibling branches): the proved callback equations do not yet count in the endpoint's closure;
replay plan reserves env-J 28000-29999. Branch kept (sibling of the candidate), worktree removed.
Launched before the loss was known: pv-join (`codex/pv-join-20261026` = candidate + pv-cb + pv-cb3 +
pv-adopt heads, IDs 26500-26799): discharge the caller's callback hypotheses by the proved source
equations so they enter the headline closure ("callbacks remaining" count). pv-runjoin7 (IDs
26800-27099) with LEAD RULING D220: after six rounds at 2 → 2 / 8 → 8 the remaining native facts are
not provable from the extraction; define one minimal `PV_RunJoin_TrustItems` structure (exact
statements, shipped locations, justification class; duplicates merged, derivable fields proved and
removed), construct the concrete Runtime/Boundary for the proof-account caller and prove
`privacy_headline_deployed_candidate (T : PV_RunJoin_TrustItems)` with the exact endpoint conclusion so
the record reads 2 → 0 and 8 → 0 with T the only premise; missing proofs listed separately as P
obligations, never folded into T; non-vacuity of T on both fixtures. That T list is the owner escalation
the target requires. Both will stall until the launcher is restored. Rows removed outright: 0. Privacy
target not yet established.

## D221 (Stream B) 2026-10-26 21:30 UTC: rw18 exhausted (V164 REDUCED, V163 OPEN), host gate ruling, cb4/srcid4/rw19 launched

pv-rw18 (`codex/cx-prover-rw-20261023`, head d1351e0a27; 100/100 Lean = 80 green/20 failed-replaced,
20/20 Kani = 16 pass/4 timeouts, no counterexample, no crates/programs change, no forbidden tokens,
frozen component manifest 71020eda20 exit 0 / 4.83 s / peak RSS 3.52 GB / swap 0, 172 declarations
standard axioms). V164 REDUCED to two exact hypotheses retained by `R1Z.ProverRw18ContextJoin.callback`:
`source_law : ops.op223 = extracted` (pv-cb3's V240) and `context_identity : extracted =
ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)` for the original whole
Rust helper (extraction obstructed; pinned Charon executable absent on the host). V163 OPEN:
`R1Z.ProverRw18ContextDataIff.criterion` is the exact residual iff (proof-byte and audit observations
equal a model output); no concrete whole-model instance and neither equation yet. Native checks on 816
cases per fixture are measurements, not whole-proof comparisons. Endpoint premises: none removed. The
last 29 of its compiles ran on the Mac (`local-cached-J` receipts under `evidence/pv-rw18-20261026/local/`,
cache /private/tmp/pv-rw-step-native-local-20261026, 1 GB) after the host workspace loss; pv-cb3 also
compiled locally (time-247xx-local.log). Kani012 scope deviation recorded as a charged diagnostic.

Host state at 21:15 UTC: Stream A's rebuild (EJR_, 567 attempts, 535 validation passes, peak 7.17 GB,
no swap) has restored `r1-privacy-build-integration-20261019/{tools/run-joint.sh,env/J.json,
evidence/sent.txt}` and `aspis-joint-20261019/{sources,objects}`; the rebuilt launcher accepts env-J IDs
5000-39999, refuses 20000-27099 as spent by Stream B (exit 65), reads sent.txt from evidence/, and has
no quiet-window block (the systemd-run shim covers it). Confirmation of a verification compile has not
arrived, so LEAD RULING (f) (pv-common.txt): no Stream B host scope until the lead creates
`pv-host-restored.flag` in the scratchpad; compile-free work meanwhile; no new local Mac compiles (24 GiB
host, two jobs already compile locally). Two anomalies in the rebuild's own audit concern privacy
modules and are passed to Stream A: `R1Z/SimCostOuterRetry6` elaborated with `sorryAx` at attempt 30431
(exit 90: an elaboration error in the rebuilt environment, the research source has no sorry) and
`R1Z/EventsR1P2` hit "(kernel) excessive memory consumption" at 30485 (the module's `card_NZ` is a theorem,
not an axiom). Neither module is imported by `PrivacyR1HeadlineDeployedReal` directly; the closure
check comes with the replay.

Launched under ruling (f): pv-cb4 (resume of pv-cb on `codex/pv-cb-20261026`, IDs 27100-27399, 69 Lean /
10 Kani: corrected op105, combined 18-row dictionary and projection groups, ops 107/109/118, then the
remaining upward pure ops; op117 only by split gates), pv-srcid4 (resume of pv-srcid3 on
`codex/pv-srcid3-20261026`, IDs 27400-27699: pending CanonicalNormalize / CanonicalTransferRecord /
PackedSelection / FinalAudit, then Checked on every admitted input, full-mapper `words` by unstubbed P6,
publicCorr and compile_call pure parts), pv-rw19 (candidate worktree, IDs 27700-27999, 100 Lean / 20
Kani: discharge `source_law` from pv-cb3's op223 law and `context_identity` by the D188 identity or P6,
then V163's concrete model instance and both equations). Six slots: cb3, join, runjoin7, cb4, srcid4,
rw19. Next free Stream B range 28000 is the replay reserve (pv-adopt), so new jobs start at 30000 only
after agreeing with Stream A, whose verification attempts use 30000+. Rows removed outright: 0. Privacy
target not yet established.

## D222 (Stream B) 2026-10-26 21:45 UTC: runjoin7 exhausted: three-field trust list proposed, conditional headline proved from T plus named P obligations

pv-runjoin7 (`codex/pv-runjoin-20261026`, head 3478e00a58; 100/100 Lean = 91 accepted / 9 elaboration
failures retained, 11 Kani = 10 value cuts passed, native factory rejected at `dlsym`; headline axioms
propext/Classical.choice/Quot.sound; no crates/programs change; no forbidden tokens). Result against
ruling D220: `R1Z.PV_RunJoin_TrustItems d` (PV_RunJoin_TrustItems.lean) has exactly three fields, all
OS/kernel-contract class: `entropy_law : ProverCommitPublicNonce40.E1 d.law` (64 successful getrandom
bytes uniform given the complete prior context), `entropy_kernel : ∀ c, d.nativeWeight c =
PV_RunJoin_E1Joint.weight 128 d.law d.frame d.coordinates c` (joint density of the 128 draws, not only
marginals), `observation : ∀ c, d.nativeObservation c = d.extractedObservation c` (native
getrandom/file/time/worker outcomes, filesystem state and the complete D159 observer payload equal the
extracted execution; explicitly NOT an equality with the security experiment). The old eight-leaf
Identity structure is proved equivalent to one outcome family plus time/workers (TrustOutcomes); the
separate filesystem and complete-view equalities are derivable by `observation_projection` and were
deleted from T. Exact statements, carriers, shipped locations (state_only_entropy.rs
`generate_for_mask_nonce` / getrandom::fill; RealR1_client.rs `prove_for_proof_accounts`) and the
consequence of each field failing are in `evidence/pv-runjoin6-20261026/trust-items.md`: this is the
owner escalation the target requires (new trust items), with my recommendation below.
`PV_RunJoin_TrustEndpoint.privacy_headline_deployed_candidate` has the exact endpoint conclusion (same
bound: modelError + 16/2^486 + freshBudget + 2·budget(2^64) + 2·charge, ≤ 1/2^109 + 1/2^137 + 1/2^454 +
… , < 1/2^100) but is proved from T PLUS a `ProofObligations` record P: source_V045, fill (V336),
ledger (V337), byte_blind (V338), selection/admission/runtime/observer installation, causal frames,
extracted-trace refinement (F3/F5/F6), release identity. So the record stays runtime/boundary 2 → 2,
fields 8 → 8, residuals 6 → 6; the worker correctly refused to report 2 → 0. Generic fixture T-models
exist; deployed-fixture (P ∧ T) non-vacuity is OPEN. Options A (OsAvailable premise) and B (public
error signal fed to both sides) remain unadopted and absent from the statement.
Recommendation to the owner: accept the three fields as the candidate privacy trust list (class T, OS
kernel contract; comparable to the getrandom trust already implicit in E1), reject any further T growth,
and treat every P obligation as proof work; decide A vs B (I recommend B, D215) before the final replay.
Relaunched pv-runjoin8 on the same branch (compile-free until the flag; its IDs come from the flag
file since 27100-27999 are allocated and Stream A keeps 30000+ until the rebuild hands it back; pv-adopt's
28000-29999 reserve untouched): shrink P, not T: selection/admission/runtime installation from PV_Src_*
and the published RunJoin interfaces, deployed-fixture non-vacuity with T hypothetical, then
initial-ledger independence and extracted-trace refinement. Stream A confirms the rebuild still fails on
missing extracted objects (R1CertBuild) and will revisit SimCostOuterRetry6/EventsR1P2 once the objects
are coherent; the SimCost module falls to Stream B if its final audit still flags it. Six slots: cb3,
join, cb4, srcid4, rw19, runjoin8. Rows removed outright: 0. Privacy target not yet established.

## D223 (Stream B) 2026-10-26 21:55 UTC: pv-join exhausted; the "31 callbacks remain" count corrected; join2 launched

pv-join (`codex/pv-join-20261026`, head c9d2b33137; 100/100 Lean = 85 passed / 15 failed-terminated, peak
RSS 3.64 GB, no swap, no Kani, no crates/programs change, no forbidden tokens; 55 new theorem axiom
reports all standard; the final audit module exited 1 because it omitted the headline import and its
corrected draft is uncompiled). Correction accepted by the lead: `ProverRwP6BodyData.refinement_of_data`
has an `ExternalFuns` value parameter, a reservation equation and the whole proof/audit data equation,
NOT a 31-element list of callback hypotheses (exact statement in evidence/pv-join-20261026/local/
26500-out.log). The "35 remain / 31 remain" figures of D187–D208 are the successful-body source-callback
inventory (success-next/final-state.json minus the P6/P7/P8 installs), and proving an already-selected
entry equal to a newly supplied source body is source correspondence, not a decrement of that
inventory. Only op229 overlapped: inventory 31 → 30 through PV_CB_Op229Source.op229_source with caller
independence proved. The aggregate caller now consumes 26 named source laws; the privacy headline
imports neither refinement_of_data nor any callback law, so no row receives headline join credit. Two
dictionary mismatches are real obligations, not naming: op81 (PV_CB_Borrow.selected vs
ProverRwSuccessBodyInterpretation.selected on the entries actually read) and op229 (PV_CB_Op229Transport
carrier vs CB3's op20 carrier). Both fixture non-vacuity obligations open. Consequence for the ledger:
rows V169–V267 "CLOSED-ON-CANDIDATE" in recount 2 remain correct as source equations, but the recount-3
column "enters headline closure" must be derived from refinement_of_data's data equation, not from the
inventory count. Launched pv-join2 (same branch; IDs from the flag file, range 35300-35599 planned):
corrected final audit, the two dictionary bridges and pending 71/100/101/110/51/120 bridges, then prove
the proof/audit data equation for both fixtures from the installed source laws (the V163 data equality,
read-only coordination with rw19), and name exactly which of the 30 inventory entries lack a source law.
Stream A agreed Stream B's env-J range 35000-39999 (runjoin8 35000-35299, join2 35300-35599); host
scopes still wait for the restoration message. Six slots: cb3, cb4, srcid4, rw19, runjoin8, join2. Rows
removed outright: 0. Privacy target not yet established.

## D224 (Stream B) 2026-10-26 21:45 UTC: rw19 ended at the gate with its budget unspent; ruling (g); rw20 launched

pv-rw19 (`codex/cx-prover-rw-20261023`, head bf81d1d222) committed nine UNCHECKED Lean drafts (concrete P6
compression-context identity carried into the caller, successful-audit invariant and full observation
transport), confirmed that pv-cb3 has no op223_source theorem yet and that the pinned Charon executable
is absent on the host, then ended with 0/100 Lean and 0/20 Kani because the restoration flag was absent
(next unused ID 27700). No forbidden tokens; no crates/programs change; nothing checked, so V164 stays
conditional and V163 open. LEAD RULING (g) (pv-common.txt): waiting at the gate is part of the job: poll
the flag every 10 minutes for up to 24 polls, keep drafting between polls, and only then report "gated:
budget unspent". Relaunched as pv-rw20 on the same branch with the same rows, IDs 27700-27999 and the
rw19 drafts to validate smallest-first when the flag opens. Six slots: cb3, cb4, srcid4, runjoin8,
join2, rw20. Rows removed outright: 0. Privacy target not yet established.

## D225 (Stream B) 2026-10-26 21:55 UTC: host launcher restored (partial cache); Stream B host scopes resume

Stream A's restoration message: the rebuilt env-J launcher (`r1-privacy-build-integration-20261019/tools/
run-joint.sh`, committed env/J.json and run2.py, sources/objects under aspis-joint-20261019) passed its
verification compile R1Z/EJR_Verification at attempt 30799 (exit 0, allowed reservation, axioms propext
only); handoff evidence/envj-rebuild-20261026/EJR_HANDOFF.md (research 45a8bc3956). Accepted IDs
5000-39999; 20000-27099 blocked as spent; 28000-29999 Stream B's replay reserve; 30000-34999 Stream A
(rebuild2 continues at 30800); 35000-39999 Stream B. The recovery is PARTIAL: 1,830 sources byte-matched,
767/800 compiles passed (765 standard axioms), 1,007 resolved sources not yet attempted, 28 latest
targets failed, 19 selected source hashes absent from the git object database (329 historical variants);
known blockers include core.fmt.Formatter from the archived Fmt source at 30628/30791, EventsR1P2.card_NZ
kernel memory (symbolic subtype cardinality needed before any retry; Stream A), SimCostOuterRetry6 proof
errors (Stream B takes it at the next free slot), CertOwnFill vs extracted-provider API mismatch, and scan
modules needing IMPORT_UNION_SCAN_INPUT. Consequence for privacy: any replay or dependency-closure claim
must state which objects came from this partial rebuild versus the jobs' own surviving caches; the final
privacy replay (pv-adopt plan, 28000-29999) cannot be coherent until the 1,007 remaining sources are
rebuilt or shown unneeded by the headline closure. Lead action: wrote pv-host-restored.flag (launcher,
per-job ranges cb4 27100-27399, srcid4 27400-27699, rw20 27700-27999, runjoin8 35000-35299, join2
35300-35599, cb3 35600-35899, cache caveat, never retry the two assigned modules). pv-cb3 was launched
before ruling (f) with 24700-24999, now blocked (exit 65); it will exhaust refusals and be relaunched on
35600-35899. Rows removed outright: 0. Privacy target not yet established.

## D226 (Stream B) 2026-10-26 22:30 UTC: cb3 exhausted (four candidate source rows), envfix launched for the two rebuilt-env failures

pv-cb3 (`codex/pv-cb3-20261026`, head 54f2ac877f; 100/100 Lean, 20/20 Kani, no crates/programs change, no
forbidden tokens; 39-module bundle and final audit on the host before the range block: exit 0, 1.08 s,
peak RSS 2.55 GiB, swap 0, standard axioms). ROW-DISCHARGED(candidate) by the D208/D211 law, composed in
`PV_CB3_CallbackBundle.opN_source`: op246 (V254, receipt 24763), op229 (V246, 24760; duplicate of pv-cb's
op229_source, to be deduplicated at recount 3), op225 (V242, 24762), op120 (V219, 24754). Op51 (V195)
withdrawn and OPEN: the native harness canonicalises through `WideExact::new`, so arbitrary
extracted-carrier correspondence is unproved; the serialization native gate is recorded as
constructor-image evidence only. Worker's running count against recount 2: OPEN 110 → 106, independent
OPEN 51 → 47, CLOSED-ON-CANDIDATE 40 → 44 (subject to the V246 dedupe and to D223: these are source
equations, not headline-closure entries). Endpoint premises removed: 0. The freed slot went to pv-envfix
(`codex/pv-envfix-20261026`, research base, IDs 35900-36199, 60 Lean): diagnose SimCostOuterRetry6 (omega
failures 31:44/46:27, type mismatch 51:12 → sorryAx at 30431) and EventsR1P2 (kernel memory at 30485,
7.17 GB) as environment-variant versus source faults by hashing each import chain against research HEAD
and the rebuild's sent list; recompile mismatched dependencies into its own objects; EventsR1P2 only by
the symbolic subtype-cardinality route, never an unchanged retry (Stream A confirmed both modules are
Stream B's). cb3's continuation (op51 arbitrary-carrier correspondence, remaining top-down ops) takes the
next free slot on range 35600-35899. Six slots: cb4, srcid4, runjoin8, join2, rw20, envfix. Rows removed
outright: 0. Privacy target not yet established.

## D227 (Stream B) 2026-10-26 22:40 UTC: envfix: both rebuilt-env failures were stale source variants; research unchanged; cb5 launched

pv-envfix (`codex/pv-envfix-20261026`, 4/60 Lean, no Kani, evidence + one audit module PV_Env_Axioms,
merged into research). Diagnosis (evidence/pv-envfix-20261026/AUDIT.md): the rebuild selected STALE
historical variants of the two target files; every strict R0Z/R1Z dependency in both import chains
byte-matches research HEAD and has a shared object. The unchanged research sources compile against the
restored objects into the job's private objects dir: SimCostOuterRetry6 attempt 35901 exit 0 / 1.75 s /
peak 3.43 GiB / swap 0; EventsR1P2 attempt 35902 exit 0 / 2.13 s / 3.44 GiB / 0; axioms audit of all 19
theorems standard. So "environment repaired, source unchanged": no research proof change, no sorry, no
cap change; AGENTS.md resource rule 5 satisfied because the retry was against changed inputs (correct
source variant), not an unchanged rerun. Downstream modules (EventsR1P3/4, AgreeR1P/2, FinalR1P,
PrivacyR1P, SimCostPass6Audit) still need replay against the correct objects; neither target is on the
current headline endpoint's import path. Stream A told: envj-rebuild2's variant selection can prefer a
historical hash over research HEAD, which bears on the remaining 1,007 entries. Launched pv-cb5
(continuation of cb3 on `codex/pv-cb3-20261026`, IDs 35600-35899, 100 Lean / 15 Kani: op51's
arbitrary-carrier correspondence first, op223 early for rw20's source_law, then the remaining top-down
ops). Six slots: cb4, srcid4, runjoin8, join2, rw20, cb5. Rows removed outright: 0. Privacy target not
yet established.

## D228 (Stream B) 2026-10-26 23:00 UTC: srcid4 exhausted; full audit blocked by 92 missing objects; srcid5 launched

pv-srcid4 (`codex/pv-srcid3-20261026`, head 34995987c0; 37/37 resumed Lean, 8/8 Kani = 2 metadata passes /
6 verification timeouts, no counterexample; no crates/programs change; no forbidden tokens; the edited
tools/r1-builder-reference files are reference/harness code and are checked for cfg(kani)-only status by
srcid5). Accepted on the host after the gate opened: canonical normalisation, the canonical transfer and
withdrawal record identities, the generalised PackedSelection; focused audit 153 standard-axiom checks.
The FULL dependency-closure audit is incomplete: the inventory lists 92 imported objects missing from the
partial rebuild, so the branch stays unmerged (merge gate = full audit with every object present and
byte-matched to research HEAD). Families: words, publicCorr, admission, row_call REDUCED (unchanged
interfaces), compile_call OPEN; PV_Src_Premises deployed 5 → 5, reference 3 (D219). The corrected combined
bridge is an unaccepted draft. One reservation retry started 28 s early; recorded and guarded. Launched
pv-srcid5 (same branch, IDs 36200-36499, 100 Lean / 6 Kani): compile the 92 missing research-HEAD objects
into the job's own objects dir, run the full audit, validate the bridge, then compile_call's pure Records
callees, publicCorr's deployed association and `words` by the variant-decomposed unstubbed mapper. Six
slots: cb4, runjoin8, join2, rw20, cb5, srcid5. Rows removed outright: 0. Privacy target not yet
established.

## D229 (Stream B) 2026-10-26 23:50 UTC: join2 exhausted (bridges checked, inventory 30 → 30), join3 launched; rebuild2 merged with HEAD-match gate

pv-join2 (`codex/pv-join-20261026`, head ce8e0224ab; 100/100 host Lean = 89 passed / 11 failed, peak RSS
4.46 GB, swap 0, no Kani, no local compiles, no crates/programs change, no forbidden tokens). Checked on
the restored host: bridges for current ops 71/100/101/110 and CB3 ops 51/120, the op81 dictionary
compatibility (PV_CB_Borrow.selected vs ProverRwSuccessBodyInterpretation.selected on the entries read),
the native op20 carrier bridge, the P6-selected ledger `BodySourceLaw`, the successful-audit guard, and the
headline import chain rebuilt with receipts; the actual transfer/withdrawal fixture source boundaries are
pinned (ed1c1cef71). Inventory 30 → 30; entries still without a source law: 4, 32-36, 79, 117, 121-123,
132-134, 222-224, 226-228, 230, 232, 249-253, 257-259. Still OPEN on both fixtures: the proof-byte
equations, the complete audit/status equations, the whole V163 equality and native non-vacuity. The
combined final audit did not run (one-attempt miscount); the original headline checked separately.
Endpoint premises removed: 0. Launched pv-join3 (same branch, IDs 36500-36799, 100 Lean, last 5 reserved
for the combined audit): baseline audit first, then per fixture the proof-byte and audit/status equations
from the installed laws with explicit reachability of inventory entries, V163 per fixture, native
non-vacuity, then source laws for entries both fixtures reach (consuming cb4/cb5 proofs). Also recorded:
Stream A's envj-rebuild2 is merged (7ccb01e1a6) with a HEAD-match gate (754/774 compiled sources equal
research HEAD byte-for-byte, 20 have no HEAD file: 17 unmerged PDict_* plus three EJS audit modules, 0
stale picks); smoke 31075 imports PrivacyR1HeadlineDeployedReal with propext only; CertOwnFill and both
Formatter consumers pass only under recorded historical profiles. The three shared sources its integrity
pass found changed were Stream B launcher recompiles of HEAD sources (join2 attempt 35312; srcid5
36300/36301) and byte-match HEAD. 669 + 501 source entries remain unattempted; no third round unless the
pv-adopt replay plan names a missing set. Six slots: cb4, runjoin8, rw20, cb5, srcid5, join3. Rows removed
outright: 0. Privacy target not yet established.

## D230 (Stream B) 2026-10-27 00:05 UTC: join3 exhausted with a green combined audit; join scope narrowed to reachability and source laws; join4 launched

pv-join3 (`codex/pv-join-20261026`, head 1ad24470b8; 100/100 host Lean = 96 passed / 4 failed, IDs
36500-36599 each used once, no Kani, swap 0, no crates/programs change, no forbidden tokens). Baseline
audit 36500 failed on a missing object; the recovered audit 36579 passed; the final combined audit 36599
passed: all 126 PV_Join_* theorems plus the headline, 127 axiom reports standard. Checked: public-caller
byte/refinement equivalence, explicit fixture-record conversions, selected-fixture ledger source laws, a
criterion against rw20's independent serialization model. Still OPEN on both fixtures: the independent
proof-byte equation, the complete model audit/status equation, the whole V163 equality and native
non-vacuity; execution reachability unknown (no inventory entry yet proved unreachable). Inventory 30 →
30; endpoint premises removed: 0. Lead decision (AGENTS.md §7, shared obstruction): three join rounds
stalled on the same missing interface, the concrete protocol-to-model instance, which is rw20's
deliverable on the candidate branch; join4 (same branch, IDs 36800-37099, 100 Lean / 6 Kani) is narrowed
to the source side: per-fixture execution reachability of the 30 inventory entries from the extracted
prover (Lean unreachability theorems, Kani traces as evidence), source laws for reached entries
(consuming cb4/cb5 proofs, never duplicating), and the fixture proof-byte equations only once rw20
publishes the model instance. Six slots: cb4, runjoin8, rw20, cb5, srcid5, join4. Rows removed outright:
0. Privacy target not yet established.

## D231 (Stream B) 2026-10-27 00:20 UTC: srcid5 exhausted (full audit green but merge gate blocked by a stale cached object); launcher outage; srcid6 launched

pv-srcid5 (`codex/pv-srcid3-20261026`, head 92d3db0b2f; 100/100 Lean all succeeded, 6/6 Kani mapper
harnesses timed out at 180 s, no counterexample; no crates/programs change; Rust changes cfg(kani)-only per
the worker, gating to be confirmed by srcid6 since several tools/r1-builder-reference files carry no
in-file cfg). Missing objects 92 → 0; full audit 132 modules, 579/579 standard axiom reports (final run exit
0, 2.38 s, 4.23 GB RSS, swap 0); combined canonical private-record/admission bridge validated with its
public-association join. MERGE GATE BLOCKED: the cached object `R1NaturalProjection` differs materially
from the research source, so the audit ran against a non-HEAD dependency; the branch stays unmerged.
Families: compile_call OPEN (pure `Records.call` equation owed), words REDUCED (unstubbed full-mapper
equality + installed checked selection), publicCorr REDUCED (root-helper equation + deployed snapshot
association), admission REDUCED (SourceSelectionContract/SelectedAdmission joins), row_call REDUCED
(InstalledTransport.endpoint_row_call). PV_Src_Premises deployed 5 → 5. Launched pv-srcid6 (same branch,
IDs 37100-37399, 100 Lean / 4 Kani): recompile every stale closure object from HEAD with dependents, full
audit, MERGE-GATE.md with per-object source-sha = HEAD-sha evidence; then Records.call, root helper,
variant-split mapper. Launcher outage 00:03-00:05 UTC: Stream A's codex-run.sh vanished from its
scratchpad (neither stream deleted it); join4's first two launches started no worker; I reconstructed a
Stream B copy (pv-codex-run.sh / pv-codex-retry.sh in my scratchpad, same codex exec line) and launched
join4 with it at 00:05; Stream A restored the original byte-equal at 00:05 and will keep the launcher
scripts in the repo under evidence. join4 is running normally. Six slots: cb4, runjoin8, rw20, cb5,
join4, srcid6. Rows removed outright: 0. Privacy target not yet established.

## D232 (Stream B) 2026-10-27 00:25 UTC: runjoin8 exhausted: constructed-candidate P shrank by two (initial, causal); deployed P unchanged; runjoin9 launched

pv-runjoin8 (`codex/pv-runjoin-20261026`, head e896c81133; 100/100 Lean = 78 accepted / 22 rejected, 8/8
Kani = 7 passed / 1 timeout, focused trust audit 1.79 s / 4.42 GB / swap 0, standard axioms; no forbidden
tokens). crates/ change: `crates/aspis-statement/src/pool_v1/pair_trace.rs` gains a `#[cfg(kani)]` mod
declaration pointing at the new harness file pair_trace_pv_runjoin8_roots.rs (bounded no-stub root checks
calling the frozen pool_v1_tree_parent); cfg(kani)-only, so excluded from every release build by
construction; it lives on a candidate-sibling branch and is covered by the candidate's ELF gate before any
adoption. Result (evidence/pv-runjoin8-20261026/P-before-after.json): the CONSTRUCTED candidate's P
record went from {identity, common_public, initial, causal, trace} to {identity, common_public, trace}:
initial-ledger independence (`ledger (initialState (coordinates.symm (t,rest))) = ledger (… (u,rest))`)
and causal frames (`frame i` depends only on draws j < i) are PROVED for the constructed candidate. T
unchanged at three fields. The DEPLOYED instance's P obligations (actual selection/compiler/admission
installation, runtime/carrier/observer installation, release identity) remain open; record counts
2 → 2 / 8 → 8 / 6 → 6; P ∧ T non-vacuity OPEN on both fixtures. Installation closure stopped at
PDict_Static222_13 (missing installation dependency from the dict branch); the compiler public-binding
obstruction is recorded exactly. Launched pv-runjoin9 (same branch, IDs 37400-37699, 100 Lean / 6 Kani):
resume the installation closure through the PDict_ objects, discharge identity/common_public for the
installed proof-account inputs using PV_Src_*/PV_Join_*, construct the fixture Runtime/Boundary for
deployed non-vacuity, then `trace` via PV_L2_*. Six slots: cb4, rw20, cb5, join4, srcid6, runjoin9. Rows
removed outright: 0. Privacy target not yet established.

## D233 (Stream B) 2026-10-27 00:30 UTC: rw20 exhausted: V164's context identity discharged, one hypothesis left; V163 model construction still open; rw21 launched

pv-rw20 (`codex/cx-prover-rw-20261023`, head 0242bd9221; 100/100 Lean = 96 passed, Kani 1/20 charged
then queue stopped on the required first configuration failure, no counterexample; no crates/programs
change; no forbidden tokens; combined component manifest audit 230 declarations, standard axioms, zero
swap, cached-component replay not a clean-source rebuild). V164: the concrete P6 context identity
(`context_identity`) is DISCHARGED in the checked consumer; V164 now rests on the single hypothesis
`P_source_p6` (the op223 source law `ops.op223 = extracted`), which neither pv-cb4 nor pv-cb5 has yet
proved. V163: the canonical audit invariant, complete observation transport, mathematical data transport
and the independent guarded assembly adapter are checked; OPEN are the deployed caller's whole-model
construction and the proof-byte equations (fixtures and general). Endpoint premises removed: 0. Launched
pv-rw21 (same branch, IDs 37700-37999, 100 Lean / 10 Kani): consume or prove the op223 law and close V164;
publish the concrete mathematical model instance early under a stable name for join4 to consume; prove
the transfer then withdrawal proof-byte equations, then the general criterion; re-freeze the manifest.
Six slots: cb4, cb5, join4, srcid6, runjoin9, rw21. Rows removed outright: 0. Privacy target not yet
established.

## D234 (Stream B) 2026-10-27 00:40 UTC: join4 stopped on an op121 disagreement; ruled not a row counterexample (non-canonical M31 input); join5 launched

pv-join4 (`codex/pv-join-20261026`, head 8eba145a71; 5/100 Lean, 6/6 Kani, final audit 36804 GREEN: 127
PV_Join theorems plus the headline, standard axioms, 1.73 s / 4.34 GB / swap 0; no crates/programs change;
no forbidden tokens). Findings: per-fixture execution-reached sets unresolved, universally unreachable set
empty (`PV_Join_PublicFailure4.fail_public` proves only a conditional serialization-panic prefix);
inventory 30 → 30, entries 4, 32, 122, 123, 232, 257 explicitly deferred to pv-runjoin; both fixture
equations open; rw20's model instance not yet published. The worker stopped on a checked disagreement:
for shipped `evaluate_state_only_polynomial` versus its proposed Horner reference, with coefficient 2 =
[1,0,0,0] and challenge [0, 2147483648, 0, 0], optimized source returns [3,0,0,0] and the reference
[2147483646,0,0,0]; Kani confirms an unsigned-subtraction overflow at crates/aspis-core/src/field.rs:331
(`a + P - b`). RETAINED as evidence (AGENTS.md §7). LEAD RULING: not a ROW counterexample. The challenge
component 2^31 exceeds P = 2^31 - 1 and so violates M31's documented representation invariant
("canonical representation in [0, P)", field.rs:22); the subtraction underflows only for non-canonical
b. The row statement (op121 selected entry = its own extracted definition, D208/D211) is untouched, as
the worker's report itself states. Consequence: the P6 owned reference's domain is the canonical
representatives, and "every M31 reaching op121 in the deployed caller is canonical" becomes a PROOF
OBLIGATION discharged from the producers (reduce_u64 < P, constructors, deserialisation checks), never an
assumption; the direct extraction route is preferred where it succeeds. No shipped-code change. Launched
pv-join5 (same branch, IDs 38000-38299, 95 Lean / 6 Kani) with this ruling, then reachability, source laws
for reached entries, and the fixture equations once rw21 publishes ProverRw21ModelInstance. Six slots:
cb4, cb5, srcid6, runjoin9, rw21, join5. Rows removed outright: 0. Privacy target not yet established.

## D235 (Stream B) 2026-10-27 00:50 UTC: cb4 exhausted: five more candidate source rows (23/73); shared Kani configuration failure; cb6 launched

pv-cb4 (`codex/pv-cb-20261026`, source head 0b0b73a21f, evidence head ff8096896d; 69/69 Lean = 66 passed /
3 failed with passing corrected replacements; Kani 1 pass then a compiler configuration failure, queue
stopped, 8 unused; no crates/programs change; no forbidden tokens; final joint audit 27168: 23 source
laws, 23 joint projections, 18 helpers, standard axioms, exit 0 / 1.72 s / 4.30 GB / swap 0; zero direct
hash mismatches in the dependency snapshot, cached transitive dependencies reused). ROW-DISCHARGED
(candidate) 18/73 → 23/73: ops 84 (V203), 105 (V206), 107 (V208), 109 (V210), 118 (V217). op117 PARTIAL,
op259 obstructed, op223 (V240, the last V164 hypothesis) not yet proved by either callback job. Endpoint
premises removed: 0. Shared obstruction (AGENTS.md §7): two jobs (cb4, rw20) stopped Kani on the same
post-rebuild "compiler configuration failure"; cb6 is told to reproduce it on a trivial harness, record
the exact error/toolchain in KANI-CONFIG.md and fix only its own host-dir configuration, else continue by
Lean. Launched pv-cb6 (same branch, IDs 38300-38599, 100 Lean / 12 Kani): op223 first under the stable
name PV_CB_Op223Source.op223_source for rw21, then op117 by split gates, op259, the remaining upward ops;
P6 references on the canonical domain with the invariant proved at call sites (D234). Six slots: cb5,
srcid6, runjoin9, rw21, join5, cb6. Rows removed outright: 0. Privacy target not yet established.

## D236 (Stream B) 2026-10-27 01:30 UTC: join5 and cb5 exhausted; op51 discharged; join track paused for recount 3; cb7 launched

pv-join5 (`codex/pv-join-20261026`, head 908f14a854; 95/95 Lean, 6/6 Kani, final audits 38092-38094
standard axioms, swap 0; no crates/programs change; no forbidden tokens). Proved canonical interpolation
outputs for the current joined caller with arbitrary raw evaluation values. op121 OPEN: direct extraction
failed; the canonical-domain owned reference compiles but both Kani equivalence checks timed out (not
rerun unchanged); the D234 counterexample is preserved. Inventory 30 → 30; per-fixture reached sets still
unresolved; both proof-byte equations open; rw21's published serializer inspected, its
deployed-input-to-Transcript association still open. Lead decision (AGENTS.md §7): five join rounds have
not moved the inventory or reachability; the join slot is paused until rw21 publishes the model instance
or recount 3 identifies a better independent row. pv-cb5 (`codex/pv-cb3-20261026`, head 29297acd5c;
100/100 Lean = 71 passed, Kani 2/15 then the shared configuration failure; frozen 39-module manifest,
final audit exit 0 / 1.55 s / 4.28 GB / swap 0, 78 axiom checks standard; no crates/programs change; no
forbidden tokens). V195/op51 ROW-DISCHARGED(candidate) for ARBITRARY extracted carriers (complete Result,
no canonicality or desired-output premise; native harness 170 checks), repairing the cb3 withdrawal.
op249: staged reference and typed kernel pass, shipped-to-reference correspondence open. op223: direct
extraction refused by Aeneas (escaping-reference loan validation), so its law goes by the P6 route (cb6).
cb3-track rows 4 → 5; candidate closures 44 → 45 before the op229 dedupe. Endpoint premises removed: 0.
Launched pv-recount3 (`codex/pv-recount3-20261027`, research base, IDs 38600-38699, statement checks
only): recount 3 of the ledger over all sibling branches with a new column "in headline closure?
(research / candidate / neither)" derived by import-chain inspection, the D223 inventory correction, the
D234 canonical-domain obligation and per-fixture reachability as new rows, dedupe op229, corrections to
D209-D235 claims, and the most valuable independent row. Launched pv-cb7 (cb3 branch, IDs 38700-38999,
100 Lean / 10 Kani): op249 correspondence and law, then the remaining top-down ops; op223 stays with cb6.
Six slots: srcid6, runjoin9, rw21, cb6, recount3, cb7. Rows removed outright: 0. Privacy target not yet
established.

## D237 (Stream B) 2026-10-27 01:35 UTC: runjoin9 exhausted: installation closure through the dictionary, constructed-candidate P down to two; runjoin10 launched

pv-runjoin9 (`codex/pv-runjoin-20261026`, head ab9f1bfb8f; 100/100 Lean = 86 accepted / 14 rejected, 6/6
Kani passed (configuration works in its host dir), three reserved focused audits standard axioms, swap 0;
no forbidden tokens; the only crates/ change extends the existing cfg(kani) child module
pair_trace_pv_runjoin8_roots.rs by 24 lines of fixed-cell root checks, excluded from release builds). The
installation closure now passes through PDict_ReachCaller (dictionary objects pinned and replayed); the
joined-selector identity (`identity`) and `common_public` are PROVED for the installed caller, so the
constructed-candidate P record is {source public binding, trace} (from {identity, common_public, trace}).
The DEPLOYED public binding remains OPEN; T unchanged (three fields); record 2 → 2 / 8 → 8 / 6 → 6; P ∧ T
non-vacuity OPEN on both fixtures with the exact missing deployment facts recorded (0dbc560f6c); 4 F5 and
21 multiproof dependency objects are missing from the shared cache. Endpoint premises removed: 0. Launched
pv-runjoin10 (same branch, IDs 39000-39299, 100 Lean / 6 Kani): actual selected compiler records and the
deployed public binding from PV_Src_*, concrete runtime/observer per fixture for non-vacuity, the 25
missing objects and the L2 source closure toward `trace`. Stream B's agreed range 35000-39999 has 700 IDs
left (39300-39999); a further range will be agreed with Stream A before it runs out. Six slots: srcid6,
rw21, cb6, recount3, cb7, runjoin10. Rows removed outright: 0. Privacy target not yet established.

## D238 (Stream B) 2026-10-27 01:45 UTC: env-J launcher range extended to 40000-49999 (range-only edit, agreed with Stream A)

Agreed split: 40000-44999 Stream B, 45000-49999 Stream A; 5000-39999 behaviour and the duplicate guard
unchanged. Edit on the host, backup `tools/run-joint.sh.bak-streamB-20261027` (sha256
c1fa8fe3cbd248ef01cf2cc7a54496bb16fe7722ad655599e31c7a60a27d6d27), new file sha256
11cc87d94e7069923fda1948c498a5e6ced8afc36a9a3c225dbdb277eeb27121, `sh -n` clean:

```diff
--- r1-privacy-build-integration-20261019/tools/run-joint.sh.bak-streamB-20261027
+++ r1-privacy-build-integration-20261019/tools/run-joint.sh
@@ -21 +21 @@
-  case "$A" in 5[0-7][0-9][0-9]|[6-9][0-9][0-9][0-9]|1[0-9][0-9][0-9][0-9]|2[0-9][0-9][0-9][0-9]|3[0-9][0-9][0-9][0-9]) ;; *) echo "attempt $A outside restored env-J ranges"; exit 64;; esac
+  case "$A" in 5[0-7][0-9][0-9]|[6-9][0-9][0-9][0-9]|1[0-9][0-9][0-9][0-9]|2[0-9][0-9][0-9][0-9]|3[0-9][0-9][0-9][0-9]|4[0-9][0-9][0-9][0-9]) ;; *) echo "attempt $A outside restored env-J ranges"; exit 64;; esac
```
Stream B's next job ranges: 39300-39599, 39600-39899, then 40000+ in blocks of 300. Privacy target not
yet established.

## D239 (Stream B) 2026-10-27 01:50 UTC: Recount 3 merged (OPEN 110 → 103, CLOSED-ON-CANDIDATE 40 → 27 after corrections); lead claims corrected; wire job launched

pv-recount3 (`codex/pv-recount3-20261027`, merged a77e372c08; 20/20 statement checks, 19 green, one
missing-object diagnostic; no proofs, no Kani; worktree and branch removed). Totals recount 2 → 3: rows
403 → 407 (T/P/C 26/376/5); OPEN 110 → 103; REDUCED 154 → 176; EVIDENCED 12 → 14 (timing D216 EVIDENCED);
CLOSED-ON-RESEARCH 87 → 87; CLOSED-ON-CANDIDATE 40 → 27. OPEN buckets a/b/c 51/50/9 → 44/51/8. New rows:
V403 (M31 canonical domain at op121 callers, D234), V404/V405 (transfer/withdrawal per-fixture execution
reachability). "In headline closure?" for the 27 candidate closures: research 0, candidate 17, neither
10: import paths are organisation, not deployed discharge. CORRECTIONS ACCEPTED by the lead: (1) 18
candidate "source closure" labels were installed/selected-reference equations, not complete
extracted-source theorems, and are REDUCED (reporting correction, no equation disproved); (2) D226 double-
counted op229 (cb and cb3); (3) D235 mapped five operation numbers to wrong row IDs: the cb4 closures are
ops 84, 105, 107, 109, 118 and their row IDs are those in ROWS3.md, not the V-numbers I wrote; (4) D219's
whole-row V269 Formatter closure is unsupported (only the axiom slice is closed; V270's scoped diagnostic
is the 27th closure); (5) D223's inventory correction is supported. Op51 is recorded OPEN at the recount's
pinned heads; the later cb5 arbitrary-carrier repair (29297acd5c) is disclosed and will be credited at
recount 4 after audit. RunJoin stays 2 → 2 / 8 → 8 / 6 → 6: the constructed-candidate reductions
(initial, causal, identity, common_public) do not reduce deployed P; T remains three proposed fields
awaiting owner adoption. Next independent target named by the recount: V240/op223 (= V164's
`P_source_p6`), already assigned to cb6. Launched pv-wire on the pv-join worktree (IDs 39300-39599, 60
Lean): merge pv-cb and pv-cb3 heads into the join branch (git-only), wire every unconsumed candidate
closure into the aggregate caller's closure with per-op consumer theorems, write IMPORT-CHAIN.md for
recount 4, combined audit. Six slots: srcid6, rw21, cb6, cb7, runjoin10, wire. Rows removed outright: 0.
Privacy target not yet established.

## D240 (Stream B) 2026-10-27 02:05 UTC: wire job done: 26 of 27 candidate closures now consumed by the aggregate caller (organisation, not discharge)

pv-wire (`codex/pv-join-20261026`, head c3b99bc9d9; 60/60 Lean, IDs 39300-39359, final audits standard
axioms, swap 0; no crates/programs change vs the candidate; no forbidden tokens). pv-cb (ff8096896d) and
pv-cb3 (29297acd5c) merged into the join branch without conflicts. Import reachability of the 27
CLOSED-ON-CANDIDATE rows from the candidate consumer closure: 17 consumed / 10 unconsumed → 26 / 1; all 26
closing source laws plus the arbitrary-carrier op51 law are applied by per-op consumer theorems; V270
stays unreachable because its scoped Formatter diagnostic has no closing operation theorem.
evidence/pv-join-20261026/wire/IMPORT-CHAIN.md gives every row's import path for recount 4. This is
organisation of proved facts into the consumer closure, not premise discharge; the research headline
imports none of it; no headline credit. Rows removed outright: 0. Privacy target not yet established.

## D241 (Stream B) 2026-10-27 02:40 UTC: srcid6 exhausted; merge gate redefined (project vs external provenance); R1NaturalProjection at HEAD does not compile; cblib launched earlier; srcid7 launched

pv-srcid6 (`codex/pv-srcid3-20261026`, head 6f0741bb10; 100/100 Lean, 4/4 Kani mapper partitions timed
out, no counterexample; no crates/programs change; no forbidden tokens in branch modules (the two `sorry`
hits are in copied upstream Aeneas.Std.Slice sources under evidence/, not ours); full audit 147 modules /
616 standard reports, three final targets exit 0 / ≤2.01 s / ≤4.27 GB / swap 0). Reference Rust gating
confirmed: parent cfg(kani) declarations, records_reference.rs under cfg(any(kani, aeneas_ref)). The
obsolete Formatter profile was rejected and quarantined, the repaired HEAD formatter rebuilt with an
empty axiom set. Families: compile_call: pure Records.call reference equation PROVED for arbitrary inputs,
deployed dictionary association OPEN; publicCorr REDUCED to the root-helper equation, 21 parent cells and
the deployed snapshot association (symbolic root recurrence proved); words: full unstubbed mapper
equality unproved (Kani route exhausted, moves to Lean); admission/row_call REDUCED (unchanged
interfaces). PV_Src_Premises deployed 5 → 5. MERGE GATE BLOCKED with a provenance inventory of 6,499
imported objects: 810 accepted source links, 48 PROJECT gaps, 5,641 EXTERNAL gaps. FINDING:
`R1NaturalProjection.lean` (docs/research/100bit-spend-path-20261013/evidence/lean-natural-projection-
20261013/remote-evidence/, Stream A's tree, unchanged since a29d480477) does NOT compile at research HEAD
under the current toolchain (unsolved goals at 28:35 and 58:67; attempts 37102, 37260); the cached object
came from a historical variant. The worker left a two-line tactic repair UNAPPLIED
(evidence/pv-srcid3-20261026/PROJECTION-REPAIR.patch); the lead has sent it to Stream A and will not
touch the file. LEAD RULING: the merge gate distinguishes PROJECT objects (must be compiled from a source
byte-equal to research HEAD) from EXTERNAL objects (Lean core, Mathlib, Aeneas backend: linked to the
pinned toolchain/lake-manifest revision, not to repository sources); the 48 project gaps are the real
blocker, the projection cone is a single named exception until research changes. Launched pv-srcid7
(same branch, IDs 40000-40299, 100 Lean / 2 Kani): MERGE-GATE v2, the 48 project gaps, words by Lean from
the variant decomposition, compile_call's deployed association, publicCorr's root helper and cells. Also
launched at 02:06 UTC (not yet logged): pv-cblib (`codex/pv-cblib-20261027`, candidate sibling, IDs
39600-39899, 100 Lean / 10 Kani) on the two independent library families nobody held: digest/SHA-2 ops
205/208/209/212/215/216/217/219 (V231-V238) and std/alloc ops 25/26/28/29/30-36 (V177-V187), against the
extracted third-party source at the pinned dependency revision, published through PV_CBL_CallbackBundle.
Housekeeping: the merged pv-l2-sim worktree and branch were removed; pv-l1 and pv-l3 are candidate
siblings and stay. Six slots: rw21, cb6, cb7, runjoin10, cblib, srcid7. Rows removed outright: 0. Privacy
target not yet established.

## D242 (Stream B) 2026-10-27 02:45 UTC: runjoin10 exhausted; the shared obstruction named (no concrete selected record of the deployed caller yet); runjoin11 launched on it alone

pv-runjoin10 (`codex/pv-runjoin-20261026`, head 623a1d3be6; 100/100 Lean = 99 accepted / 1 corrected
rejection, 6/6 Kani passed, root cells 19/21; three focused trust audits standard axioms, swap 0; no
forbidden tokens; crates/ change = 24 more cfg(kani)-only lines in the existing child module). Proved:
packed-record public preservation, conditional admission bridges, compiler-payload uniqueness; the 25
originally missing F5/multiproof objects restored (0 left; 11 further L2 objects missing). Constructed
P stays {source public binding, trace}; deployed P OPEN; T unchanged; record 2 → 2 / 8 → 8 / 6 → 6; P ∧ T
non-vacuity OPEN. Endpoint premises removed: 0. Lead assessment (AGENTS.md §7): runjoin8-10, srcid5-6 and
the join rounds all stop at the same missing interface: nobody has exhibited the ACTUAL selected record
of the deployed proof-account caller (D162) as a concrete Lean term together with its compiler-return
equation and public-transition association; everything downstream (deployed public binding, runtime
installation, non-vacuity, V163's model instance, srcid's admission/row_call) is conditional on it.
Launched pv-runjoin11 (same branch, IDs 40300-40599, 100 Lean / 4 Kani) with that single deliverable per
fixture (transfer, then withdrawal), from the pinned fixture bytes and PV_Src_CanonicalTransferRecord; any
genuine missing fact is to be stated as one exact proposition with its shipped location rather than
bridged around. Six slots: rw21, cb6, cb7, cblib, srcid7, runjoin11. Rows removed outright: 0. Privacy
target not yet established.

## D243 (Stream B) 2026-10-27 02:55 UTC: correction to D241: R1NaturalProjection was a wrong-source comparison and a shared-source overwrite by srcid6, now restored

Stream A's resolution: module `R1NaturalProjection` is pinned (lean-semantic-prefix-agreement-20261015/
import-source-pins.json) to docs/research/100bit-spend-path-20261013/lean/NaturalProjection.lean (sha256
add9c506d5cb…), which compiles fresh in the current toolchain (rebuild attempt 30200, object 6cf99b13…);
the file under evidence/lean-natural-projection-20261013/remote-evidence/ (sha 41db583fe503…) is a
historical artifact, not the source of the current closure. D241's finding "R1NaturalProjection at HEAD
does not compile" is therefore WITHDRAWN as stated: the remote-evidence copy does not compile, the pinned
source does; the "stale cached object" flagged by srcid5/6 was the CORRECT object and the comparison
used the wrong file. Incident: at 02:02 UTC my srcid6 worker copied the remote-evidence variant over
the shared `aspis-joint-20261019/sources/R1NaturalProjection.lean` (attempts 37102/37260 compiled that
copy and failed); the shared object was never replaced. Restored at 02:55 UTC by the lead to the add9c5
content (sha verified; the wrong copy kept under codex-pv-srcid-20261026/ as evidence); Stream A informed;
no patch applied anywhere. LEAD RULING (h) added to pv-common.txt: resolve module names through the pin
table; never overwrite a shared source with a different variant; stop and report if the shared source
differs. pv-srcid7 (launched 02:34 under the superseded D241 wording) will treat the projection cone as an
exception until it re-reads; its next round closes it with the pinned source. The merge-gate ruling of
D241 (project vs external provenance) stands. Rows removed outright: 0. Privacy target not yet
established.

## D244 (Stream B) 2026-10-27 02:50 UTC: rw21 exhausted: model-instance serializer published, V164/V163 unchanged; rw slot given to a third callback family (cbmid)

pv-rw21 (`codex/cx-prover-rw-20261023`, head 237e135561; 100/100 Lean = 60 pass / 40 fail, 10/10 Kani =
2 pass / 6 timeouts / 1 MIR overflow assertion / 1 configuration rejection, no row counterexample; no
crates/programs change; no forbidden tokens; three final audits 477 declarations standard axioms,
cached-component replay). Published `R1Z.ProverRw21ModelInstance`: a checked mathematical transcript
serializer (installed serializer output for bounded arbitrary slices equals its mathematical byte image;
finite sequence encoding; bounded endpoint/no-pole transport). V164: {P_source_p6} → {P_source_p6} (the
op223 complete-Result law is not yet available; cb6 holds it). V163: deployed model construction, both
fixture byte equations and the general equation OPEN: the serializer still awaits the deployed-input
protocol construction, i.e. the same shared obstruction named in D242 (the actual selected record of the
deployed caller), now runjoin11's single deliverable. Endpoint premises removed: 0. Lead decision: no
rw22 until cb6 publishes op223 or runjoin11 publishes the fixture records (AGENTS.md §7); the slot goes to
pv-cbmid (`codex/pv-cbmid-20261027`, candidate sibling at 237e135561, IDs 40600-40899, 100 Lean / 10
Kani) on bucket-a rows no live job holds: V228-V230 (pool_v1 pair-forest hiding ops 132-134), V201 (op79
encoder eval_message), then V239/V241 if cb7 has not reached them; laws via PV_CBM_CallbackBundle. Six
slots: cb6, cb7, cblib, srcid7, runjoin11, cbmid. Rows removed outright: 0. Privacy target not yet
established.

## D245 (Stream B) 2026-10-27 03:00 UTC: runjoin11 stopped at the exact missing source fact: the shipped records leaf has no extraction; runjoin12 launched on it alone

pv-runjoin11 (`codex/pv-runjoin-20261026`, head 458a0c1ff2; 5/100 Lean all accepted, 2/4 Kani passed,
root cells 21/21; three focused trust audits standard axioms, swap 0; no forbidden tokens; 8 cfg(kani)
lines added to the existing child module). It pinned the literal transfer/withdrawal public records and
transitions from the ed1c1cef71 fixture bytes (PV_RunJoin_RecordedTransfer / RecordedWithdrawal) and then
stopped, as instructed, at ONE exact missing fact (evidence/pv-runjoin11-20261027/stage1-missing-fact.md,
stage2-missing-fact.md): the shipped records leaf `records` (crates/aspis-statement/src/pool_v1/
pair_forest_copy_builder.rs:227-270, via CopyRecords::new and pair_forest_trace.rs:275) has NO extraction
in the Lean closure: BuilderForestAdmissionPort.lean:4362 declares `class Records` as an opaque class
parameter and :4376 sets the source leaf to `sourceRecords.call`; the owned reference
PV_Src_RecordDynamic.dictionary is not identified with that leaf, and its complete-Result equation
(srcid6) does not establish the identification. The missing proposition, on the SAME fixture arguments
(witness from deterministic_input_witness_v1, recipient digest(300)/digest(400)/600, change
digest(500)/digest(600)/400, snapshot r0_fixture::prepare(false)): `Records.call R_shipped w 600 (some
recipient) change snapshot 77 = @PV_Src_RecordDynamic.call E_shipped w 600 (some recipient) change
snapshot 77`, where R_shipped is the (absent) extraction of the actual Rust function. Downstream and still
OPEN: `@PV_Src_NativeInput.run E_shipped R_shipped i = .ok (.Ok i.compiled)` and the transition equality at
the actual selected i; deployed public binding; non-vacuity; constructed P {source public binding, trace}
unchanged; record 2/8/6; T unchanged. This is the shared obstruction of D242 made exact: a missing
source-refinement proof, not a cryptographic assumption (AGENTS.md §3). Launched pv-runjoin12 (same
branch, IDs 40900-41199, 100 Lean / 12 Kani) on that single deliverable: route A direct Charon/Aeneas
extraction of `records`; route B the P6 link through the existing tools/r1-builder-reference/
records_reference.rs (Kani shipped = reference, no stubs, bounded; extraction of the reference), recorded
as a P6 gate; then the identification per fixture, compiler-return and transition equations. Six slots:
cb6, cb7, cblib, srcid7, cbmid, runjoin12. Rows removed outright: 0. Privacy target not yet established.

## D246 (Stream B) 2026-10-27 03:15 UTC: cb6 exhausted with no new rows; Kani root cause and timeouts; ruling (i); cb8 launched on op223 alone

pv-cb6 (`codex/pv-cb-20261026`, head 148ce95eec; 100/100 Lean = 77 passed / 23 rejected; all 12
substantive Kani gates timed out at 180 s, no verdict, no counterexample; no crates/programs change; no
forbidden tokens; joint audit 226 declarations standard axioms, 38404-38406, ≤1.91 s / 4.28 GB / swap 0).
No row discharged: op223 (V240) OPEN with `CompressCanonical.reference`, its array-domain and tag
invariants and the compressor caller transport proved but no source association (Aeneas refuses the
direct extraction; the shipped = reference gates timed out); op117 PARTIAL (split native gates timed
out); op259/op258 OPEN (circle and pole gates timed out). Kani configuration (KANI-CONFIG.md): the
post-rebuild failure is rustc codegen `failed to spawn work thread: Os { code: 11, WouldBlock }` inside
the TasksMax=64 scope (Kani 0.67.0, rustc 1.93.0-nightly 53732d5e0); a dependency-free probe passed;
mitigation `taskset --cpu-list 0-3` limits compiler fan-out without touching caps. Two scheduling
deviations recorded (five early gates before the matched reproduction; one Lean/Kani overlap). LEAD
RULING (i): a 180 s Kani timeout may be retried once at up to 900 s (the launcher's own Lean timeout)
under the same memory caps and TasksMax with taskset, then split or move to Lean; never a third identical
run. Launched pv-cb8 (same branch, IDs 41200-41499, 100 Lean / 12 Kani) on op223 alone: 900 s gates,
then a borrow-free cfg(aeneas_ref) shim as the extraction target if Aeneas still refuses the shipped
function, publishing `PV_CB_Op223Source.op223_source` under that stable name for rw22; fallback
op117/op259/op258 under ruling (i). Six slots: cb7, cblib, srcid7, cbmid, runjoin12, cb8. Rows removed
outright: 0. Privacy target not yet established.

## D247 (Stream B) 2026-10-27 05:00 UTC: srcid7 exhausted: merge gate v2 down to 3 project gaps, projection exception closed; srcid8 launched

pv-srcid7 (`codex/pv-srcid3-20261026`, head e0d5c21c56; 100/100 Lean, 2/2 Kani (internal-linear
comparison passed 514 checks; full-helper prefix comparison timed out, no equality inferred); no
crates/programs change; no forbidden tokens in branch modules; full audit 164 modules / 658 unique
standard-axiom reports). MERGE GATE v2 under D241: project gaps 48 → 3 (879 project objects), external
objects 5,640 each linked to the env-J toolchain and Aeneas backend @ 220c7ff9 / manifest pins, 0
manifest gaps; the R1NaturalProjection exception is CLOSED under ruling (h) with the pinned source
(receipt 30200 matches current HEAD and the current object; nothing changed). Remaining gaps: no
accepted receipt binds the current object to the expected HEAD source for
AspisFormal.V6PublishedTheoremInterfaces (904f5e5b…), R0P.LogUpChain (a9b0e52d…), R0P.SemRounds
(564b9026…). Proved: the complete candidate mapper transcription equality and the canonical
internal-linear source/copy equality; new RunJoin records pinned. OPEN: deployed mapper identification,
installed compiler association (both wait on runjoin12's records identification), the 21 Lean
root-parent cells. PV_Src_Premises deployed 5 → 5. Launched pv-srcid8 (same branch, IDs 41500-41799, 60
Lean / 2 Kani): the three gaps first (resolve via the pin table, compile from HEAD with dependents,
full audit, MERGE-GATE "CLEAN" so the lead can merge), then the 21 cells, the deployed identification
from runjoin12's publication, and the prefix comparison under ruling (i). Six slots: cb7, cblib, cbmid,
runjoin12, cb8, srcid8. Rows removed outright: 0. Privacy target not yet established.

## D248 (Stream B) 2026-10-27 06:45 UTC: owner adopts all seven Stream B recommendations; actions taken

The owner: "agree with all your recommendations". Recorded in design/PRIVACY-LEDGER-20261026.md "Owner
decisions 2026-10-27 (B)". (1) T = the three fields of PV_RunJoin_TrustItems adopted as the privacy trust
list and CAPPED (no new T field; native facts become P). (2) OS-failure repair option B adopted (failure
signal public to both experiments, bound unchanged), conditional on proving the failure event
witness-independent, now a P obligation. (3) V371: enable DOITM and accept V371 only in DOITM mode. NOT
ENABLED: the build host runs Secure Boot, kernel lockdown (integrity) refuses `wrmsr -a 0x1b01 1`
("Lockdown: wrmsr: raw MSR access is restricted"); ARCH_CAPABILITIES 0xdc9fd6b has the DOITM bit;
UARCH_MISC_CTL = 0 on all 22 CPUs. Needs a firmware/kernel change the lead cannot make remotely; V371
stays a substantive trust item meanwhile. (4) Inversion zero-boundary: proof work (try_inv operands
nonzero on witness-bearing paths outside charged bad events). (5) Docker caps shrunk at runtime with
`docker update` (reversible; compose files under ~/crypto-tax/infra and ~/maths-revision/services still
hold the old values and would restore them on recreate): crypto-tax-worker-1 6144 → 2560 MiB (peak 1304),
latex-server-latex-server-1 4096 → 512 MiB (peak 92), crypto-tax-reports-1 2048 → 512 MiB (peak 218);
swap limits kept at 2× memory; crypto-tax-db-1 (peak 7784 of 8192), api, hausklar, gateway, link
unchanged; finite container caps 24,576 → 15,872 MiB, about one more 8 GiB scope under the 55 GiB
barrier. (6) Client bundle: pin client-pins.json in the release ledger: handed to Stream A, who own that
file. (7) Archival: deleted, after a sha256 manifest of all 4,060 files (evidence/pv-archive-20261027/
deleted-files.sha256, manifest sha256 8bb802cd…), the invalidated codex-pv-rebase-20261026/
corpus-overparallel-v2 (6.2 GiB) and the superseded smoke-baseline/candidate-001 and
phase-paired-002-baseline/candidate (16.9 GiB) under codex-cx-prover-rw-20261023; corpus-1000-002 and
focused-paired-001 kept; nothing had them open. Host free 620 → 643 GiB. Worker rule (j) added. New jobs
queued for the next free slots: option B endpoint (statement + witness-independence of the failure event)
and the inversion zero-boundary proof. Rows removed outright: 0. Privacy target not yet established.

## D249 (Stream B) 2026-10-27 06:55 UTC: Stream A's contract amendment noted for privacy

Stream A reports an owner-approved amendment to SECURITY-CONTRACT-20261021.md ("Owner-approved
amendment, 2026-10-27", research 503f682c76): the D188 Aeneas extraction trust item is read at TRACE
fidelity (the pinned translation preserves the accepted Result and the chronological attempted
digest-call sequence of the extracted monadic execution, same body/inputs/replies/pins, no new Lean
axiom). Privacy arguments cite D188 by that name and do not restate it. The soundness trust inventory
(design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md, approved) covers soundness surfaces only; the privacy
trust surfaces are the separately adopted T (D248: three PV_RunJoin_TrustItems fields) plus V371. Route A
(translator re-pin) was not approved. Stream A's session moved to a new address; the D248 handoffs (client
bundle pin, Docker caps) were re-sent there. Privacy target not yet established.

## D250 (Stream B) 2026-10-27 06:50 UTC: Mac disk full; five idle Stream B worktrees removed (branches kept)

Creating the pv-optb/pv-inv worktrees failed with "No space left on device" (Mac data volume 99%, 8.9
GiB free; each checkout of this repository is about 7.8 GiB). No running worker was affected (no disk
errors in any of the six worker logs). Freed 42 GiB (now 51 GiB free) by removing the worktrees of five
IDLE Stream B branches, each checked clean (no tracked changes, no untracked files, no process using
them): pv-join (c3b99bc9d9), pv-l3 (3d19f820c9), pv-rebase (b7f1f3c470), cx-prover-dict (615d347232),
cx-prover-rw (the candidate, 237e135561); all five BRANCHES are kept unchanged (none merged into research;
the candidate stays unmerged until its adoption gates pass), and the finished rw18 local Lean cache under
/private/tmp. A future job on any of them recreates its worktree. The option-B and inversion jobs (D248)
create their worktrees when their slots open. Rows removed outright: 0. Privacy target not yet
established.

## D251 (Stream B) 2026-10-27 07:05 UTC: cb8 exhausted: op223 still open by both routes; diagnosis of the shared obstruction; ruling (k); option-B job launched

pv-cb8 (`codex/pv-cb-20261026`, head 7599dff5b2; 100/100 Lean = 80 passed / 20 rejected; 12/12 Kani all
timed out, exit 124, no verdict, no counterexample: compress16 canonical/reference at 900 s unwind 18,
four per-lane compress16 splits and four Horner splits at 180 s, circle_sample_reference and
pole1024_reference at 900 s; no crates/programs change; no forbidden tokens; final audits 41300-41302
standard axioms, ≤1.65 s / 4.30 GB / swap 0). Proved: the canonical sixteen-value compressor producer
invariant, the actual legacy/forest tuple-constructor invariants, the numerical compressor caller
transport (conditional canonical16). NOT proved: `PV_CB_Op223Source.op223_source`; the transparent
by-value shim extraction fails with `ProverRwRngExtractor006: fail-closed preflight: escaping reference
output requires loan validation`. V164 unchanged: {P_source_p6} (with P_proof_bytes and the reservation
equation from the consumer); rows 23/73; endpoint premises removed 0. LEAD DIAGNOSIS (AGENTS.md §7, the
third round at the same point): the shipped function (crates/aspis-statement/src/logup.rs,
`compress_tagged_tuple(tag, values: &[M31], lambda) = lift(tag) + Σ λ^(i+1)·values[i]`) is a tiny pure
fold. Kani fails because sixteen chained bit-precise QM31 multiplications are SAT-hard (the same cause
as the op117/op258/op259 timeouts), so no bound or split will finish; the extraction fails on the slice
iterator's borrowed element (`for value in values`), not on the arithmetic. LEAD RULING (k): no Kani
shipped = reference gates for chained field arithmetic; such rows go to Lean on an extraction. The two
real routes for op223 are (i) make the pinned extraction accept slice iteration (the Aeneas backend
models core.slice.iter; the refusal is the pipeline's own fail-closed preflight) and (ii) under the D187
prover rewrite route, a prover-local index-loop copy of the function (verifier bytes untouched, since the
shared aspis-statement function is also used on SBF), which would require re-running the candidate's
differential, fixture and timing gates. A focused diagnosis job will compare both before any source
change; (ii) would come to the owner only if it changes verifier bytes, which by construction it does
not. Launched pv-optb (`codex/pv-optb-20261027`, research base, IDs 41800-42099, 100 Lean / 6 Kani): the
option-B endpoint statement with its diff against privacy_headline_deployed, the witness-independence
proof of the OS-failure event (a counterexample stops it and selects option A), and the derivation. Six
slots: cb7, cblib, cbmid, runjoin12, srcid8, optb. Rows removed outright: 0. Privacy target not yet
established.

## D252 (Stream B) 2026-10-27 07:25 UTC: cb7 exhausted (rows 5 → 5); extraction-obstruction diagnosis launched

pv-cb7 (`codex/pv-cb3-20261026`, head a436dadfee; 100/100 Lean, 10/10 Kani; final replay 38842 exit 0 /
2.13 s / 4.29 GB / swap 0, 382 axiom outputs over 372 targets all standard; no crates/programs change; no
forbidden tokens). No new row: the cb3-track count stays 5. Proved support: the shipped pole-comparator
correspondence, complete pole-reference Result laws, sampler-reference rank / canonicality / nonzero
results, typed weight-read index domains; an emitted 18-function tensor closure awaits Lean checking.
Native callback associations remain open, and its report isolates "source loan obstructions": the same
extractor refusal as op223 (D251). Since the obstruction is now shared by at least two tracks, the freed
slot goes to pv-extract (new branch `codex/pv-extract-20261027` from pv-cb @ 7599dff5b2, reusing the idle
pv-cb worktree to save disk; IDs 42400-42699, 60 Lean, no Kani): inventory every row blocked by
`ProverRwRngExtractor006`, find the preflight and why it was added, test whether the pinned Charon/Aeneas
accept the functions on a copy of the pipeline (diagnostic; use for a row only with an argument that the
preflight's concern does not apply), close op223/V164 if so, otherwise a design comparison of repairing
the extraction versus prover-local index-loop copies under D187 (verifier path unchanged; candidate gates
to re-run). Six slots: cblib, cbmid, runjoin12, srcid8, optb, extract. The inversion job (D248) takes the
next slot in the idle pv-cb3 worktree. Rows removed outright: 0. Privacy target not yet established.

## D253 (Stream B) 2026-10-27 07:30 UTC: cbmid exhausted (0 rows; reference equations only); inversion job launched

pv-cbmid (`codex/pv-cbmid-20261027`, head 8483406290; budget exhausted; three final audits 40743-40745
standard axioms, ≤1.03 s / 2.65 GB / swap 0; no crates/programs change; no forbidden tokens). No row
discharged: PV_CBM_CallbackBundle publishes REFERENCE equations for ops 132/133/134 (V228-V230: reference
selection and inventory cardinality proved), not opN_source laws; the native shipped = reference
comparisons for 133 and 134 timed out at 180 s and 900 s (launched before ruling (k)); op79 (V201)
extraction and caller invariants open; ops 222/224 prepared only. Next deliverable named: op132's
shipped/reference association with inventory uniqueness and completeness, which under ruling (k) goes
by Lean on an extraction. Launched pv-inv (D248 owner decision: inversion zero-boundary; new branch
`codex/pv-inv-20261027` from research, reusing the idle pv-cb3 worktree; IDs 42100-42399, 100 Lean / 10
Kani): inventory every inversion call site reachable from the deployed caller with operand provenance,
prove witness-bearing operands nonzero outside an already-charged bad event, or stop on a checked
witness-dependent zero (a protocol leak for the owner). Six slots: cblib, runjoin12, srcid8, optb,
extract, inv. Rows removed outright: 0. Privacy target not yet established.

## D254 (Stream B) 2026-10-27 07:45 UTC: srcid8 exhausted; merge gate held on three Stream A shared sources; srcid9 launched (Lean only)

pv-srcid8 (`codex/pv-srcid3-20261026`, head 3873ce854e; 60/60 Lean, 2/2 Kani both timed out at 900/180 s,
no counterexample; no crates/programs change; no forbidden tokens; full audit 207 modules / 727 standard
reports / swap 0; 46 objects recompiled into its own objects dir). Proved: exact owned external-layer
Result equality; the source round recurrences instantiated at the frozen 4/14/4 constants. Source parent
cells 0/21 (the 21 RunJoin mathematical cells are pinned read-only); deployed PV_Src_Premises 5 → 5;
shipped Records and installed compiler associations still missing (runjoin12). MERGE GATE v2 still
BLOCKED on 3 project gaps, now characterised exactly: the shared env-J sources for
AspisFormal.V6PublishedTheoremInterfaces (shared 80610f3a…, HEAD 904f5e5b…; compiled by Stream A attempt
30037), R0P.LogUpChain (89e6f147… vs a9b0e52d…; 30159) and R0P.SemRounds (84cd1819… vs 564b9026…; 30161)
differ from research HEAD and from every recent committed version of those paths; research changed the V6
file in 6c1455a61e. The worker left them untouched (ruling (h)); the lead has asked Stream A which source
is authoritative. Launched pv-srcid9 (same branch, IDs 42700-42999, 100 Lean, no Kani per ruling (k)):
the 21 source root-parent cells and the root-helper equation in Lean from the pinned mathematical cells,
the merge gate once Stream A answers, Records from runjoin12 if published. Six slots: cblib, runjoin12,
optb, extract, inv, srcid9. Rows removed outright: 0. Privacy target not yet established.

## D255 (Stream B) 2026-10-27 07:55 UTC: the three "project gaps" were a wrong-source comparison again; ruling (h) corrected

Stream A: the shared copies of AspisFormal.V6PublishedTheoremInterfaces (80610f3a…), R0P.LogUpChain
(89e6f147…) and R0P.SemRounds (84cd1819…) byte-match research HEAD files under the selected soundness
cohort, docs/research/100bit-spend-path-20261013/lean/bridge-selected-current-20261018/accepted-current/…,
which is where these module names resolve for the env-J closure (rebuild attempts 30037/30159/30161,
selected at d6dd1ca963). The lead verified all three sha256 prefixes against those files at HEAD and
found the resolution in evidence/envj-rebuild-20261026/EJR_final-inventory.json. So D254's "three project
gaps" were not gaps: srcid8 compared against same-named files at other paths (AspisFormal/AspisFormal/…,
docs/research/v8-r0-sem-proof-20261008/lean/R0P/…). Cause: lead ruling (h) named the 2026-10-15
import-source-pins.json as the authority, and that table maps these names to the other files: the
worker followed the ruling correctly; the ruling was wrong. Correction (h') in pv-common.txt: the
authority is the rebuild's own resolution record (EJR_final-inventory.json and the rebuild2 record); a
grep hit or the older table is not a resolution. Second same-pattern error today (D243), so a module name
is never a file identity in Stream B instructions. Merge gate: with the correct resolution, the three are
expected CLEAN; srcid9 will rewrite MERGE-GATE.md under (h') and, if every project object then matches,
the lead merges codex/pv-srcid3-20261026. Stream A asked that the accepted-current objects not be
recompiled or overwritten; if the privacy closure needs the newer variants (e.g. a declaration added in
6c1455a61e), that is a separate cohort built privately and named to Stream A. Rows removed outright: 0.
Privacy target not yet established.

## D256 (Stream B) 2026-10-27 07:55 UTC: cblib exhausted: four library rows by the P6 route; cblib2 launched

pv-cblib (`codex/pv-cblib-20261027`, head c35956a836; 100/100 Lean, 10/10 Kani with three bounded
passes, no counterexample; final manifest 39731 exit 0 / 1.05 s / 2.62 GB / swap 0, 185 declarations
standard axioms; no forbidden tokens). crates/ change: one `#[cfg(kani)] mod pv_cblib_library_checks`
appended to crates/aspis-r1-cost-probe/src/host_commitment.rs (178 lines, harness-only, excluded from
release builds; candidate-sibling branch). Rows supplied by the P6 route (owned Rust reference extracted
by Aeneas; shipped = reference by a no-stub Kani check; dictionary entry = extracted reference by rfl in
PV_CBL_CallbackBundle): V177 op25 PathBuf deref and V180 op29 PathBuf as_ref (both the identity borrow on
the frozen PathBuf carrier; std/src/path.rs sha256 14fd4134…), V185 op34 Vec::is_empty and V186 op35
Vec::default (alloc/src/vec/mod.rs sha256 a9cfdfc0…). Lead review: the laws are P6-route closures, not
extractions of the shipped library functions; recount 4 must class them as such and judge the bounded
Kani links (loop-free functions, so the bound is not material) and the PathBuf/Path carrier resolution.
op32 keeps its allocator-effect deferral. Endpoint premises removed: 0. Launched pv-cblib2 (same branch,
IDs 43000-43299, 100 Lean / 8 Kani for loop-free links only): remaining std/alloc ops 26/28/30/31/33/36,
then the SHA-2/digest family V231-V238 in Lean on the extraction of the backend the deployed x86_64
prover actually compiles (no silent substitution of the soft backend). Six slots: runjoin12, optb,
extract, inv, srcid9, cblib2. Rows removed outright: 0. Privacy target not yet established.

## D257 (Stream B) 2026-10-27 08:00 UTC: extraction obstruction resolved by diagnosis; op223 route (ii) adopted as a D187 candidate change; pv-op223 launched

pv-extract (`codex/pv-extract-20261027`, head 258c685f50; 60/60 Lean = 54 pass / 6 fail, no Kani; final
42460 exit 0 / 1.77 s / 4.31 GB / swap 0, 47 standard axiom outputs; no crates/programs change; no
forbidden tokens). Findings (evidence/pv-extract-20261027/INVENTORY.md, ROOT-CAUSE.md): fifteen callback
ops are refused by the pinned extractor's fail-closed guard (rng-extractor/base/src/Main.ml:745-761,
which scans all function output types including helpers): 36, 79, 132, 133, 205, 212, 215-217, 219, 222,
223, 224, 249, 258; op253 has a separate internal shared-loan failure. The guard is not the real
obstruction: with it removed in a private copy, the pinned Aeneas fails in InterpReduceCollapse.ml:1991
(shared-borrow abstraction-ID remapping during loop-context matching) and emits no Lean; a fresh Charon
accepts op223 but Aeneas still emits nothing. Route (i) (repair the extraction) therefore needs an
Aeneas fix with its own invariant, and the soundness-side translator re-pin was not approved by the owner
(Stream A, 2026-10-27). Route (ii) works: an index-loop compressor passes the UNCHANGED pinned extractor
with the guard on (23 functions, 3 constants, zero opaque), and `PV_Ext_ClosedCandidate.candidate_reference`
proves complete-Result equality to the P6 compressor for arbitrary inputs. LEAD DECISION: adopt route
(ii) for op223 only, as a candidate change under the owner-approved prover rewrite route D187: the patch
(evidence/pv-extract-20261027/route-ii-op223.patch, 18 lines) adds a private module in
crates/aspis-r1-cost-probe behind `prover` and `r1p-check` and redirects the one host call in
host_semantic::copy_endpoint_values; aspis-core, aspis-statement, programs/ and the shared logup.rs
function are untouched, so the verifier keeps the original. Adoption still requires: all three ELF pins
reconfirmed (any difference stops adoption and goes to the owner), byte-identical fixture proofs, ≥1,000
paired whole-prover differential runs, and the quiet-window timing gate (median < 15 s, ≤ +10%), which
the lead schedules with Stream A. The other affected ops stay design-only (table in
design/PV-EXTRACT-20261027.md) until op223 has gone through the whole workflow. Launched pv-op223
(`codex/pv-op223-20261027` from the extraction branch, reusing the pv-cb worktree; IDs 43300-43599, 100
Lean, no Kani): apply the patch, extract the applied host function with the unchanged tool, prove
op223_source and the bridge that discharges V164's P_source_p6, run gates (a)-(c), write the timing plan.
Six slots: runjoin12, optb, inv, srcid9, cblib2, op223. Rows removed outright: 0. Privacy target not yet
established.

## D258 (Stream B) 2026-10-27 08:05 UTC: inversion round 1 merged (V380 open, no leak found); inv2 launched

pv-inv (`codex/pv-inv-20261027`, research-based; 100/100 Lean = 79 successful, 10 Kani = 9 passed / 1 CLI
rejection; final three audits standard axioms over 145 declarations, peak 4.12 GB, swap 0; no
crates/programs change; no forbidden tokens) merged into research (4bdd2679c8); worktree reused, branch
deleted. Inventory of every inversion site reachable from the deployed caller with operand provenance
(evidence/pv-inv-20261027/INVENTORY.md). Proved locally: guarded packed operands, extracted QM31/CM31
norm nonzero conditions, interpolation denominators, registry-slot uniqueness, interleaved packing. No
checked witness-dependent zero (no leak found). V380-inversion OPEN: the native registry enumeration,
tuple-bank reads, tags and active masks are not yet bound to the model, and containment of the zero
events in the headline's existing bad-event union is not yet instantiated. Launched pv-inv2 (new branch
`codex/pv-inv2-20261027` from research in the same worktree; IDs 43600-43899, 100 Lean / 6 Kani for
control only): the native bindings, then containment against a named term of the existing bound, or a
checked counterexample for the owner. Six slots: runjoin12, optb, srcid9, cblib2, op223, inv2. Rows
removed outright: 0. Privacy target not yet established.

## D259 (Stream B) 2026-10-27 08:40 UTC: inversion round 2 merged: zero events contained in the existing poleBad; inv3 launched

pv-inv2 (`codex/pv-inv2-20261027`, research-based; 100/100 Lean, 6/6 Kani control checks passed; final
audits 181 theorems standard axioms, swap 0; no crates/programs change; no forbidden tokens) merged into
research (5222276e4a). Proved: conditional native tuple/inverse bindings for the inversion descriptor
banks, registry activity facts, packing safety, and SAME-COIN CONTAINMENT of the inversion zero events in
the EXISTING HVZK event `poleBad` (R0Z/HvzkS.lean, HvzkV.lean; its mass bound `poleBad_mass_le` already
feeds the headline), with the retained charge 8 · (4096 / ((2^31 − 1)^4 − 1)): the bound, simE and the
observer are unchanged. Still OPEN for V380: the installed registry/bank/coupling bindings (partly on
runjoin12's records), mask blocks 48-63, and the complete observation law of the inversion branches. No
witness-dependent zero (no protocol leak) found. Launched pv-inv3 (new branch `codex/pv-inv3-20261027`
from research in the same worktree; IDs 43900-44199, 100 Lean / 6 Kani control only): mask blocks 48-63,
the bindings that do not need the selected record, the observation law, or a checked counterexample for
the owner. Six slots: runjoin12, optb, srcid9, cblib2, op223, inv3. Rows removed outright: 0. Privacy
target not yet established.

## D260 (Stream B) 2026-10-27 08:50 UTC: source-identification branch merged (merge gate CLEAN); publicCorr source half closed; V403 job launched

pv-srcid9 (`codex/pv-srcid3-20261026`, head 2e8351f033; 100/100 Lean = 78 accepted / 22 rejected drafts, no
Kani; final audits 42802-42804 exit 0 / ≤1.90 s / ≤4.33 GB / swap 0, 807 standard axiom reports; 6,662
audited object hashes unchanged; no crates/programs change; no forbidden tokens in branch modules).
Proved: the 21 SOURCE root-parent cells (0 → 21/21) through the frozen permutation, and the actual
root-helper equation at the explicit dictionary and the named E_shipped adapter: the publicCorr family's
SOURCE half is closed (source public-root premise removed in the source-identification instance); the
deployed snapshot / Records association stays REDUCED; compile_call OPEN; words, admission, row_call
REDUCED; deployed PV_Src_Premises 5 → 5. MERGE GATE v2 CLEAN under ruling (h'): 1,028 project objects
with zero gaps (the three D254 "gaps" resolve to the accepted-current cohort), 5,640 external objects
linked to the toolchain/manifest pins; no Stream A source or object changed. The lead merged
codex/pv-srcid3-20261026 into research (d0fafc7254, no conflicts) and removed its worktree and branch.
The merged tools/r1-builder-reference/pv_srcid3.rs is a cfg(kani)-reachable reference module in a tools
crate that no workspace or shipped crate includes. GitHub warned about large files on push (warning
only; evidence corpora). The source track now waits on runjoin12's R_shipped. Launched pv-canon
(`codex/pv-canon-20261027`, research base, IDs 44200-44499, 100 Lean / 6 Kani control only) on V403: every
M31/CM31/QM31 reaching op121 on the deployed path is canonical (producers inventoried and proved, field
operations preserve canonicality, composed over the extracted caller), and the op121 row obligation on
the canonical domain stated exactly. Six slots: runjoin12, optb, cblib2, op223, inv3, canon. Rows removed
outright: 0. Privacy target not yet established.

## D261 (Stream B) 2026-10-27 09:05 UTC: inversion round 3 merged; inversion track paused on its dependencies; recount 4 launched

pv-inv3 (`codex/pv-inv3-20261027`, research-based; 100/100 Lean = 97 pass / 3 corrected failures, 6/6
control-only Kani; final audits standard axioms, swap 0; no crates/programs change; no forbidden tokens)
merged into research (a6cd27379d), branch deleted. Proved: the model mask gap for blocks 48-63 closed, the
full mask table, row-order/dedup transport, conditional same-coupling guard containment and Boolean trace
laws; retained charge exactly 8 · (4096 / ((2^31 − 1)^4 − 1)) inside the existing poleBad. V380 still OPEN
on the native dynamic registry/schedule refinement, the selected caller and the complete D159
observation law; no protocol counterexample. These depend on runjoin12's selected-record identification
(D245) and on the extraction route for ops 132/133 (D251/D257), so per AGENTS.md §7 the inversion track
pauses until one of them lands rather than a fourth round against the same dependencies. Launched
pv-recount4 (`codex/pv-recount4-20261027` from research in the reused pv-cb3 worktree; IDs 44500-44599,
statement checks only): recount 4 with the D248 owner decisions applied to the T/P/C classes, a P6 versus
extraction split of candidate closures, the headline-closure column set from the wire IMPORT-CHAIN, a new
bucket for rows blocked by the shared extraction obstruction, and corrections to D236-D261. Six slots:
runjoin12, optb, cblib2, op223, canon, recount4. Rows removed outright: 0. Privacy target not yet
established.

## D262 (Stream B) 2026-10-27 09:10 UTC: option B round 1; the witness-independence condition made precise (off the charged bad events); optb2 launched

pv-optb (`codex/pv-optb-20261027`, head b654d6d8b1; 100/100 Lean = 52 pass / 48 fail, no Kani; three
reserved audits exit 0, ≤4.97 s, ≤4.27 GB, swap 0, standard axioms; no crates/programs change; no
forbidden tokens; four memory-killed attempts (41830/41832/41834/41843) on concrete finite-function-space
cardinality, caps not raised, replaced by an abstract Nat.card proof that checks in 1.98 s / 4.1 GB).
Stated `privacy_headline_deployed_B`: same simE, observer map and bound; a different theorem with a fixed
public failure signal (evidence/pv-optb-20261027/STATEMENT-DIFF.md). Proved: the emitted caller stops on
its first Entropy callback error; extracted retry-control results; independence on named failure
prefixes; a conditional synchronisation theorem for PV_RunJoin_Deployed.execute; and a family of admitted
same-public witnesses whose pole sets differ (41850/41851), so for some challenge their NoPole verdicts
are opposite. Not proved: witness-independence of every reached deployed OS failure. A native
programmed-oracle probe differing in reached failure used a malformed compilation and a programmable
oracle, so it is explicitly not an admitted-witness counterexample. LEAD RULING: the job's condition
`Independent` (equal reached failure observation for ALL admitted same-public pairs at the same world
and coins) is stronger than the adopted condition and is expected to be false: later OS calls are
reached only after a Rejected attempt, and rejection depends on the witness through the pole set. The
headline already charges exactly that dependence (the HVZK chain's real and ideal loops agree off
`poleBad`, whose mass bound feeds the headline, alongside the fresh-query, seed and fuel events). The
D215 condition, made precise, is IndependentOffBad: off the union of the headline's existing charged bad
events, the reached failure observation is a function of public input, OS world and coins. This is not a
weakening: simE, the observer and the bound are unchanged; witness-dependent retries stay paid for inside
poleBad (the same pattern as the inversion containment, D259). Option A is selected only by an
admitted-witness counterexample with the fixed HOST_HASH oracle OUTSIDE every charged event. Launched
pv-optb2 (same branch, IDs 44600-44899, 100 Lean / 4 Kani control only): state IndependentOffBad naming
only existing events, prove it for the emitted retry body, derive the B headline, or stop on that
counterexample. Six slots: runjoin12, cblib2, op223, canon, recount4, optb2. Rows removed outright: 0.
Privacy target not yet established.

## D263 (Stream B) 2026-10-27 09:20 UTC: cblib2 exhausted (library rows 4 → 5); SHA-2 rows reduced to the dispatcher question; cblib3 launched

pv-cblib2 (`codex/pv-cblib-20261027`, head 7aebfd030c; 100/100 Lean, 8/8 Kani = 6 bounded passes / 2
timeouts, no counterexample; final audits 43098-43100 exit 0, ≤8.00 s / 2.63 GB / swap 0, manifest of 151
modules / 506 declarations standard axioms; no forbidden tokens). crates/ change: 71 lines in two further
top-level `#[cfg(kani)]` modules of crates/aspis-r1-cost-probe/src/host_commitment.rs (verified: the
file's only additions are three cfg(kani) modules at lines 376-623; excluded from release builds). New
row by the P6 route: V179 op28 String as_ref Path (`PV_CBL_CallbackBundle.op28_source`; native gate
covers valid UTF-8 strings of length 2 with arbitrary byte index; recount 4 to judge the bound). SHA-2:
the extracted SOFT backend's round/schedule helpers, feed-forward addition and whole-block totality are
proved in Lean (no SHA Kani gate, ruling (k)); the block-value composition and the link to the backend
the deployed x86 prover actually runs remain open: the pinned sha2 dispatches at runtime to SHA-NI
instructions (cpufeatures), which are not extractable and could enter only as a trust item, which the
owner capped (D248). Launched pv-cblib3 (same branch, IDs 41588-41799 = the never-used tail of srcid8's
range): the remaining std/alloc rows 26/30/31/33/36, the soft block composition and V231-V238 on the soft
backend, and design/PV-SHA-DISPATCH-20261027.md with measured options (a soft-backend prover build under
D187 with the projected timing cost; a Lean model of SHA-NI and what it would trust; others) and a
recommendation, without changing the build. Env-J: Stream B's 40000-44999 is nearly allocated; a further
range was requested from Stream A. Six slots: runjoin12, op223, canon, recount4, optb2, cblib3. Rows
removed outright: 0. Privacy target not yet established.

## D264 (Stream B) 2026-10-27 09:20 UTC: env-J launcher range extended to 50000-59999 (range-only edit, agreed with Stream A)

Agreed split: 50000-54999 Stream B, 55000-59999 Stream A; 45000-49999 stays Stream A's; 5000-49999
behaviour, the 20000-27099 block and the duplicate guard unchanged. Host edit with backup
`tools/run-joint.sh.bak-streamB-20261027b` (sha256 11cc87d94e7069923fda1948c498a5e6ced8afc36a9a3c225dbdb277eeb27121,
= the D238 version); new file sha256 7ac8a13e34b33d2cb41b3ef4bf52e97498fe744b48010069950c63d6dd980c66;
`sh -n` clean:

```diff
@@ -21 +21 @@
-  case "$A" in 5[0-7][0-9][0-9]|[6-9][0-9][0-9][0-9]|1[0-9][0-9][0-9][0-9]|2[0-9][0-9][0-9][0-9]|3[0-9][0-9][0-9][0-9]|4[0-9][0-9][0-9][0-9]) ;; *) echo "attempt $A outside restored env-J ranges"; exit 64;; esac
+  case "$A" in 5[0-7][0-9][0-9]|[6-9][0-9][0-9][0-9]|1[0-9][0-9][0-9][0-9]|2[0-9][0-9][0-9][0-9]|3[0-9][0-9][0-9][0-9]|4[0-9][0-9][0-9][0-9]|5[0-9][0-9][0-9][0-9]) ;; *) echo "attempt $A outside restored env-J ranges"; exit 64;; esac
```
Privacy target not yet established.

## D265 (Stream B) 2026-10-27 09:25 UTC: Recount 4 merged (OPEN 103 → 95, CLOSED-ON-CANDIDATE 27 → 35); op134 job launched

pv-recount4 (`codex/pv-recount4-20261027`, merged 4103b624f8; 20/20 statement checks, 16 passed, three
missing-object failures and one helper namespace error retained; no proofs, no Kani; branch deleted after
confirming it is in research). All 407 rows re-derived; original rows preserved. Totals recount 3 → 4:
OPEN 103 → 95; REDUCED 176 → 176; EVIDENCED 14 → 14; CLOSED-ON-RESEARCH 87 → 87; CLOSED-ON-CANDIDATE
27 → 35. Closure routes of the 35: 27 extracted operation laws, 1 extraction bridge, 6 P6 gates (the
library rows; bounded links and the Path carrier qualified), 1 axiom diagnostic (V270). Headline
membership of the candidate closures: research 0, candidate consumer 29, neither 6 (the original 27
reproduce the wire job's 0/26/1). OPEN buckets a/b/c/d (d = blocked by the shared extraction
obstruction, new): 23/55/1/16, change −21/+4/−7/+16; the single remaining owner-first blocker is DOITM
(V371). D248 applied: the three trust fields class T (adopted, capped), option B's condition a P row,
inversion P. Corrections recorded: the wrong-source withdrawals of D243/D255 preserved; op229
deduplicated; bounded P6 links and Path carriers qualified; op36 adapter failures distinguished from the
shipped generic conversion; V164/V240 count as one callback decrement. Next independent rows named: V403
(canonical domain, pv-canon running), V400 (option-B failure synchronisation, pv-optb2 running), V230/op134
(source correspondence). Launched pv-op134 (`codex/pv-op134-20261027` from pv-cbmid's branch in the
reused pv-cb3 worktree; first IDs of Stream B's new range 50000-50299; 100 Lean / 4 Kani control only):
direct extraction of the shipped function with the unchanged tool and its source law, or, if the tool
refuses it, the exact refusal, a route (ii) design entry and the complete reference side. Six slots:
runjoin12, op223, canon, optb2, cblib3, op134. Rows removed outright: 0. Privacy target not yet
established.

## D266 (Stream B) 2026-10-27 09:55 UTC: option B round 2 merged (IndependentOffBad stated over existing events; native instance open); L3 disassembly audit launched

pv-optb2 (`codex/pv-optb-20261027`, research-based; budget exhausted; three focused audits 44897/44898/44702
exit 0, ≤4.74 s / 4.27 GB / swap 0, standard axioms; no crates/programs change; no forbidden tokens) merged
into research (6c88a07f9c); worktree and branch removed. `IndependentOffBad` is stated as ruled in D262:
∀ w u, pub w = pub u → ∀ os coins, ¬bad w os coins → ¬bad u os coins → signal w os coins = signal u os coins,
where `bad` is the union of EXISTING charged events only (poleBad, HitEv, CollEv, lazyBad, exhQ, realFresh,
realBad, seedGuess, fuel failure). Proved: public-decoder equivalence, off-pole retry-index agreement,
emitted attempt-control lemmas, a conditional deployed synchronisation, complete first-draw failure
equality, and joint failure transport that preserves the existing charges. OPEN: the concrete native
instance (reachable-state body/public-verdict synchronisation at the fixed HOST_HASH; association of the
actual failure metadata with the charged coordinates) and the endogenous privacy_headline_deployed_B;
the earlier B theorem remains the fixed-signal form. No qualifying native counterexample. These remain
on the native interpretation (bucket b), so the B track pauses (AGENTS.md §7) until runjoin12 lands.
Launched pv-l3dis (existing `codex/pv-l3-20261026`, worktree recreated; IDs 50300-50599, 30 Lean, static
analysis only) on V373, the L3 disassembly audit of the prover as it ships for x86_64 Linux:
exact build identity, every secret-dependent kernel and call site disassembled from the built binary,
findings per site (clean / secret-dependent branch / secret-dependent address / variable-latency op /
relies on V371 because DOITM is off), any secret-dependent branch or address reported as a checked
finding; never a claim of absence of leakage. Six slots: runjoin12, op223, canon, cblib3, op134, l3dis.
Rows removed outright: 0. Privacy target not yet established.

## D267 (Stream B) 2026-10-27 10:05 UTC: runjoin12 exhausted; the records leaf blocks only on closures; closure-free rewrite adopted as a D187 candidate change; runjoin13 launched

pv-runjoin12 (`codex/pv-runjoin-20261026`, head dd58cab637; 100/100 Lean = 88 kernel successes / 12
rejected, 12 verification runs; three reserved audits standard axioms; no new crates/programs change
beyond the existing cfg(kani) child module; no forbidden tokens). R_shipped NOT established. Route A
(direct extraction of the shipped `records`, byte-identical to ed1c1cef71, sha256 e1315ebd…) fails in
Aeneas with "missing FnOnce at core/function.rs:250, FunsAnalysis.ml:134" (receipts pv12-records-charon-18,
pv12-aeneas-25). Route B (Kani shipped = reference) incomplete: only the external-layer and
raw-conversion helper gates passed; the mapper equality timed out. Proved: both REFERENCE fixture
equations, all frozen empty-root parent cells and the table recurrence, the fixture input commitment
through named permutation cells, the nullifier inverse and frozen root words. Lead reading of the source
(pair_forest_copy_builder.rs:227-270): `records` is pure field shuffling, two closures
(`rec.map(|r| …).unwrap_or(ZERO8)` and `core::array::from_fn(|l| …)`) and one call to pair_empty_roots();
the extraction blocker is the closures, the Kani blocker the Poseidon empty-root computation (already
proved in Lean cell by cell). LEAD DECISION under D187: rewrite THAT ONE FUNCTION closure-free with
identical semantics (explicit match and an index loop; no other change). Because pool_v1 is compiled into
the Pool and Registry programs, gate (a), all three ELF pins rebuilt and confirmed, runs FIRST; any pin
change stops the work and goes to the owner (the builder is witness-side and is expected to be dropped
from the programs by the linker, which the gate checks rather than assumes). Gates (b) fixture bytes and
(c) the 1,000-run differential will run once over this change together with the op223 change (D257),
followed by the quiet-window timing gate. Launched pv-runjoin13 (same branch, IDs 50600-50899, 100 Lean /
2 Kani): edit, gate (a), extraction with the unchanged tool, R_shipped, the identification per fixture
and generally, then compiler-return, transition, deployed public binding and non-vacuity. Six slots:
op223, canon, cblib3, op134, l3dis, runjoin13. Rows removed outright: 0. Privacy target not yet
established.

## D268 (Stream B) 2026-10-27 10:10 UTC: L3 disassembly round 1: checked secret-dependent branches classified; shipped binary not yet audited; l3dis2 launched

pv-l3dis (`codex/pv-l3-20261026`, head 5eba6495dd; 0/30 Lean, no Kani; capped release build 67.1 s / 932
MB / swap 0; no crates/programs change). Built the unmodified r1p_retry_gate EXAMPLE (release,
features optimized-terminal,ct-host-prover; rustc 1.94.1, LLVM 21.1.8, x86_64 Linux; sha256
c7f359d4da1c5a759a3ddf4b83c7cccd602b9e0c104e85170a593f82116b516a) and audited the linked disassembly
(evidence/pv-l3-20261027/DISASSEMBLY-AUDIT.md). CHECKED findings: F1/F2 private-mask rejection branch in
SeedExpander::m31 (state_only_hiding.rs:424-426: a 31-bit candidate equal to P is rejected); F3 cursor
addressing that depends on the rejection history (:409-416); F4 witness-dependent pole verdict branch at
0x9483d; F5 operand-zero branches in M31::inv; F6 a gamma-sampler carry branch on the raw Fiat-Shamir
answer; F7 seed zero/short-circuit comparisons in `generate` (state_only_entropy.rs:193); DIV in sumcheck
on public operands; ct_pole::all_slots_clear and logup::compress_tagged_tuple clean in body (V371 for
ALU/IMUL/SSE timing; DOITM off). LEAD ASSESSMENT: F1-F3 and F7 are rejection-sampler patterns that reveal
only rejection counts (probability 2^-31 per word, 2^-256 per seed), independent of the accepted mask
values and of the witness, so they are simulatable in principle: that is exactly ledger row V354 (L2 F3
SeedExpander) and V352 (generate_for_mask_nonce), which must PROVE it; F4 differs between witnesses only
on the charged poleBad event; F5 is covered by the inversion containment (D259/D261); F6 depends on public
data. No new leak is claimed or excluded: audits never prove absence of leakage. V373 stays OPEN because
the audited binary is a diagnostic example, not the shipped executable, and it lacks the 64-byte
generate_for_mask_nonce route. Launched pv-l3dis2 (same branch, IDs 50900-51199, 30 Lean): build
devnet_spend exactly as pinned by client-pins.json (release ledger, owner-approved client bundle) and
audit every secret-dependent kernel reached from devnet_spend::main, including generate_for_mask_nonce,
mask application/balancing and the hashing internals on secret data, each finding linked to its L2/L3
row; new non-rejection findings are reported as such. Six slots: op223, canon, cblib3, op134, runjoin13,
l3dis2. Rows removed outright: 0. Privacy target not yet established.

## D269 (Stream B) 2026-10-27 10:15 UTC: shipped-binary audit blocked by a missing release pin (native client build recipe and toolchain); l3dis3 launched on the devnet recipe of record

pv-l3dis2 (`codex/pv-l3-20261026`, head 22b24ffe12; no Lean, no Kani, no host scopes; no source change)
validated all 1,295 pinned client files at 5228877938 and stopped without guessing: client-pins.json (the
owner-approved client bundle in the release ledger) pins the SOURCE of the devnet_spend route but not the
native BUILD (no root rust-toolchain, no complete features, flags or command), so no binary can be named
"the shipped binary". Also: the candidate prover (the one meant to ship after adoption) differs from the
pinned client source in 26 files and lacks 6, so the client pin must be refreshed at candidate adoption.
The recipe of record is the devnet R1 run (2026-10-20, evidence/devnet-r1-20261020/README.md:55-63):
`cargo build --manifest-path tools/r1-cost-probe/Cargo.toml --release --offline --locked -j 4 --features
r1p-check --bin devnet_spend` with the host's default toolchain. Recommendation sent to Stream A (owner
of the release ledger): pin the native client build recipe and an exact toolchain (rustc/cargo, target,
RUSTFLAGS) in the client-bundle subsection, and re-pin the bundle at candidate adoption. Launched pv-l3dis3
(same branch, IDs 51200-51499, 30 Lean): build devnet_spend with the recipe of record from (A) the pinned
client source and (B) the candidate source, audit every secret-dependent kernel reached from its entry
(generate_for_mask_nonce, mask application/balancing, host semantic bodies, hashing on secret data),
results labelled "devnet R1 recipe, toolchain unpinned", findings linked to their L2/L3 rows, the
differing files mapped to kernels, and a V374 dudect plan for (B). Six slots: op223, canon, cblib3, op134,
runjoin13, l3dis3. Rows removed outright: 0. Privacy target not yet established.

## D270 (Stream B) 2026-10-27 10:25 UTC: client build recipe recorded in the release ledger; toolchain pin escalated to the owner with a recommendation

Stream A added "Native client build: recipe of record, toolchain NOT pinned" to the release ledger's
client-bundle section: the devnet R1 command (release, offline, locked, -j 4, --features r1p-check, --bin
devnet_spend, RUSTFLAGS `-C link-arg=-Wl,--threads=4` from the receipt wrapper, host default
~/.cargo/bin/cargo), "the shipped client binary" undefined until an exact toolchain pin is approved, L3
client-binary results labelled "toolchain unpinned", and the bundle re-pinned at candidate adoption.
Choosing the toolchain defines a release artifact, so it is an owner decision. Host facts (2026-10-27
10:20 UTC): the default is the MOVING `stable` channel, currently rustc 1.94.1 (e408947bf 2026-03-25,
commit e408947bfd200af42db322daf0fadfe7e26d3bd1), LLVM 21.1.8, cargo 1.94.1 (29ea6fb6a 2026-03-24),
host/target x86_64-unknown-linux-gnu. LEAD RECOMMENDATION to the owner: pin exactly that toolchain
(rustc/cargo 1.94.1 by version and commit, target x86_64-unknown-linux-gnu, RUSTFLAGS as recorded, no
target-cpu change) as the client build, because it is the toolchain the candidate's timing, differential
and L3 evidence were produced with, and pinning anything else would invalidate that evidence; record it
as a rust-toolchain file for the client build and in the release ledger; the pin is re-confirmed at
candidate adoption. Privacy target not yet established.

## D271 (Stream B) 2026-10-27 10:30 UTC: V403 round merged (canonical producers proved; caller transport open); cb9 launched on extractable independent callback rows

pv-canon (`codex/pv-canon-20261027`, research-based; 100/100 Lean = 74 passed / 26 rejected, 6/6 Kani =
5 control/indexing passes / 1 CLI rejection; audits 44497-44499 standard axioms, ≤3.15 s / 4.30 GB / swap
0; no crates/programs change; no forbidden tokens) merged into research (16191fd042), branch deleted.
Proved: canonicality of every producer of op121's arguments and `op121_arguments` over the exact
extracted interpolation/semantic/update/read prefix; `reached_canonical` composes it with the explicit,
still-open `P_NativePrefixBinding`. The whole recursive caller transport failed kernel checks and is
archived (not rerun unchanged). V403 OPEN on the recursive call-event/prefix transport and the binding to
the installed RunJoin caller. op121's remaining source obligation, stated exactly: canonical inputs give a
successful canonical output with degree-27 polynomial meaning, i.e. complete Result equality with the
proved Horner reference; op121 is in the extraction-obstruction set, so its source link is a route (ii)
question. Track paused on the RunJoin binding. Launched pv-cb9 (new branch from codex/pv-cb3-20261026
in the reused pv-canon worktree; IDs 51500-51799, 100 Lean / 4 Kani control only) on the independent
open callback rows NOT in the extraction-obstruction inventory: ops 226, 227, 228, 230, 250, 251, 252,
254, 259, by direct extraction with the unchanged tool, recording any new refusal. Six slots: op223,
cblib3, op134, runjoin13, l3dis3, cb9. Rows removed outright: 0. Privacy target not yet established.

## D272 (Stream B) 2026-10-27 10:40 UTC: L3 audit of the devnet client binary: two material side-channel findings (N1 non-CT pole comparison, N7 decimal JSON parsing of secrets); release-recipe decisions escalated

pv-l3dis3 (`codex/pv-l3-20261026`, head 63b8e1ff76; no Lean, no Kani; five capped scopes sequential;
cargo targets deleted; no source change). Artifact A (pinned client source 5228877938, devnet R1 recipe,
host rustc 1.94.1, toolchain unpinned) built: sha256 dc31d28c3eb9a793f9e2a8c81e69611b42aa8c2cace1393845cd554d090c357b.
Artifact B (candidate 237e135561) failed before compiling: tools/r1-cost-probe/Cargo.lock is stale against
the candidate's workspace changes and the recipe uses --locked (the candidate's earlier gates built
through other manifests). The pinned chain draws real entropy (devnet_spend::main → plan::prove →
RealR1_client::prove_for_proof_accounts → generate_for_mask_nonce); the deterministic fixture constructor
is compiled in (the tool enables aspis-prover/insecure-spend-fixture) but is not on the chain. New
findings in A (evidence/pv-l3-20261027/dual/AUDIT.md), lead classification:
- N1 MATERIAL. host_semantic.rs:292 `clear &= chi != *value` over every active compressed witness slot:
  the derived QM31 inequality compiles to limb-by-limb short-circuit branches (0xbd6a0/0xbd6a6/0xbd6ac).
  chi is public, values are witness-derived; the branch path differs whenever a slot's leading limb
  equals chi's (≈ 2^-31 per active slot, far above the charged poleBad and the 2^-100 target), and then
  reveals a witness-derived limb and its slot position to a timing observer. The candidate's
  constant-time replacement crate::ct_pole::all_slots_clear (audited clean in body in D268, V371 caveat)
  is compiled ONLY with the non-default feature ct-host-prover, which the recipe of record does not
  enable; the pinned research source has no CT path at all. So the devnet route as built leaks at L3.
- N7 MATERIAL. devnet_spend.rs:16 parses the request JSON, including private witness/key fields, as
  decimal integers via serde_json (de.rs:462-507): first-digit and digit-count branches make each
  secret byte's timing depend on whether it is < 10, < 100 or ≥ 100 (~1.6 bits/byte to a timing
  observer). Input decoding was never inside the constant-time kernel discipline.
- N2-N6: guard branches (zero/sum guards state_only_hiding.rs:259-266, canonical-column guards
  host_semantic.rs:60-68, private balance equalities prover.rs:139-154, helper-sum short circuits,
  sumcheck boundary checks host_sumcheck.rs:64,75) whose outcome is constant on valid honest runs; each
  is a correctness obligation on its L2 row (V354/V357/V360), not a leak if the invariant holds.
Owner escalation (release recipe; Stream A owns the ledger): the release client build must (i) be the
candidate with ct-host-prover enabled, (ii) not enable insecure-spend-fixture, (iii) use the pinned
toolchain (D270), and (iv) decode private inputs in constant time (fixed-width encoding, e.g. hex or raw
bytes, with a constant-time decoder) instead of decimal JSON numbers: a host-client change under D187
plus the Python orchestration that writes the request. Launched pv-l3dis4 (same branch, IDs
51800-52099): minimal offline lockfile repair for the tool (registry versions/checksums must not change),
build B with the recommended recipe (r1p-check + ct-host-prover), audit B side by side with A (N1 removed
by the CT path? N7 extent; N2-N6 constancy obligations), and the V374 dudect plan for B. Rows removed
outright: 0. Privacy target not yet established.

## D273 (Stream B) 2026-10-27 10:45 UTC: cblib3 (library rows 5 → 7; soft SHA block composition proved; SHA-NI escalated) and cb9 (every remaining direct-extraction target refused); route (ii) feasibility job launched

pv-cblib3 (`codex/pv-cblib-20261027`, head 4aaa5ae9a2; 100/100 Lean, 6/6 Kani; audits 41797-41799, 243
imports / 735 axiom queries standard; crates/ changes only inside existing cfg(kani) modules; no
forbidden tokens). New rows by the P6 route: V181 op30 String::with_capacity, V182 op31 String::push_str
(library list 5 → 7; native bounds explicit). Proved: the complete extracted SOFT SHA-256 word-block value
composition (schedule, 64 rounds, feed-forward), padding-reference totality, retained-buffer/reset shape.
V231-V238 open; op26/33/36 open; op32 deferred (allocator effect). Dispatcher packet
(design/PV-SHA-DISPATCH-20261027.md): the measured host selects runtime SHA-NI; 3,149,033 SHA callbacks per
proof; weighted soft/native ratio 7.91×; forcing the soft backend projects +5.93 s (≈ 19.6-19.9 s per
proof against historical baselines), which FAILS the 15 s / +10% prover gate; worker recommends keeping
SHA-NI and proving its refinement, which needs the SHA-NI instruction semantics as a trust item.
OWNER ESCALATION (lead recommendation below in the owner report). pv-cb9 (`codex/pv-cb9-20261027`, 0/100
Lean, 0/4 Kani, no theorem added) found every remaining independent direct-extraction target refused by
the unchanged extractor: escaping-reference and structured-Drop refusals for ops 226, 227, 228, 250, 251;
escaping reference for op230; a concrete path-module Drop root for op252; nested-loop return / Option
language item for op254; op259 already proved on pv-cb (SKIP). The shared extraction obstruction (D251,
D257) therefore blocks about 25 callback rows, most of what remains. Launched pv-route2
(`codex/pv-route2-20261027` from the extraction branch, reusing the pv-canon worktree; IDs 52100-52399, 60
Lean): an extractable variant per blocked function as a patch (in-place where the crate or function is
absent from the programs, else prover-local with the caller chain), each run through the UNCHANGED
extractor and type-checked, and design/PV-ROUTE2-20261027.md with the total change size, the ELFs each
change could touch, and at most three gated batches with the rows each unblocks; no patch applied.
Launched pv-cblib4 (same cblib branch, IDs 52400-52699): soft-backend SHA-2 rows (padding, byte
compression, digest wrappers) and op26/33/36, no SHA-NI work pending the owner. Six slots: op223, op134,
runjoin13, l3dis4, route2, cblib4. Rows removed outright: 0. Privacy target not yet established.

## D274 (Stream B) 2026-10-27 10:50 UTC: records closure rewrite passes the ELF gate; next extraction blocker is a borrow; bounded borrow-to-copy authorization; runjoin14 launched

pv-runjoin13 (`codex/pv-runjoin-20261026`, head 9128568ac0; 0/100 Lean, 0/2 Kani: stopped correctly for a
ruling, not exhausted). Commit 2910da23a3 rewrites the two `Option::map(..).unwrap_or(ZERO8)` closures
of `records` as `match` and the two `core::array::from_fn` closures as indexed `while` loops over 20
entries (diff evidence/pv-runjoin13-20261027/shipped-records.diff, +20/−4, nothing else). Gate (a): all
three ELFs rebuilt from that source MATCH their pins (default f8c0ec72…, devnet 63ad3e9c…, Pool 121f3e29…;
gate-a.json): the on-chain programs are byte-identical. Extraction then stops at records:230
(InterpAbs.ml:1955) on `let pair = &input.pair`. The worker proposed the one-line change
`let pair = input.pair;` and stopped because the prompt authorised only closure replacements. Lead check:
input.pair has type PoolV1PairInputNoteWitnessV1, which derives Clone, Copy (pair_trace.rs:71), and
every later use reads fields, so the copy is the same value. LEAD AUTHORIZATION (bounded): inside
`records` only, semantics-preserving repairs of two kinds: (i) a shared borrow of a Copy value replaced
by a copy (with matching `&x` arguments), (ii) closure/combinator removal; each recorded with its Copy
derive location; all three ELFs re-gated once after the last change; any blocker needing another kind of
change stops that route with the exact blocker reported. The combined gates (b) fixture bytes and (c)
1,000-run differential follow over op223 + records (GATE-PLAN.md). Launched pv-runjoin14 (same branch,
IDs 50600-50899 unused so far): the repairs, gate (a), extraction, R_shipped, identification per fixture
and generally, compiler-return, transition, deployed public binding, non-vacuity. Six slots: op223,
op134, l3dis4, route2, cblib4, runjoin14. Rows removed outright: 0. Privacy target not yet established.

## D275 (Stream B) 2026-10-27 10:55 UTC: records Copy repair passes the ELF gate; next blocker is a range loop; authorization widened to the enumerated mechanical repairs; runjoin15 launched

pv-runjoin14 (`codex/pv-runjoin-20261026`, head 503344e60f; 0/100 Lean, 0/2 Kani: stopped on a blocker
outside its authorization, not exhausted). 05cb63a2ea replaces `let pair = &input.pair` with
`let pair = input.pair` (PoolV1PairInputNoteWitnessV1 derives Copy, pair_trace.rs:71); gate (a) after the
final change: all three ELF pins MATCH. Extraction clears the borrow and stops at the unsupported
`ub_checks<bool>` of the inlined range iterator of `for level in 0..24` (core/iter/range.rs:984-986,
InterpExpressions.ml:1512); the worker proposed an index `while` loop and stopped. Lead decision: one
blocker per job cycle is waste (AGENTS.md §7), so the authorization (still confined to the function
`records`) now covers three enumerated mechanical, semantics-preserving repair kinds, as many as
extraction needs: (i) borrow-to-copy on Copy values, (ii) closure/combinator removal, (iii) `for i in
a..b` → index `while` loop with identical body, bounds and order; each recorded; the three ELFs re-gated
once after the last change; a blocker of another kind or in another function stops the route.
Launched pv-runjoin15 (same branch, IDs 50600-50899 still unused). Six slots: op223, op134, l3dis4,
route2, cblib4, runjoin15. Rows removed outright: 0. Privacy target not yet established.

## D276 (Stream B) 2026-10-27 11:00 UTC: candidate client audited (N1 removed by the CT path; N7 remains); candidate lacks the proof-account client route; rebase3 launched

pv-l3dis4 (`codex/pv-l3-20261026`, head aafc302223; no Lean/Kani; five capped scopes; no Rust or Lean
source change). Lockfile repair 1f02f0ecd7: tools/r1-cost-probe/Cargo.lock gains only the
aspis-r1-cert-build → aspis-r1-cert-check path edge (+3 lines); all 423 registry records, versions and
checksums identical. Artifact B = candidate + repaired lockfile, built with the RECOMMENDED recipe
pending owner approval (r1p-check + aspis-r1-cost-probe/ct-host-prover, --locked, host rustc 1.94.1,
toolchain unpinned): exit 0, 177.5 s, peak 1.98 GB, swap 0, sha256
898005412d46103cfeffe5740f7892ee01d1e3d73a7293338c62e679445b5e67. A/B comparison: N1 REMOVED in B (the
reviewed constant-time pole scan; only the final verdict branch remains); N2-N6 remain in both (guard
outcomes constant on valid honest inputs: proof obligations on the L2 rows); N7 REMAINS in both
(decimal JSON parsing of private key bytes: about 7 conditional jumps for a zero byte, 10/13/16 for 1/2/3
digit bytes); no fixture-feature-gated API is linked or reached in B, but local deterministic NOTE
fixtures of the devnet tool remain reachable. NEW: in B, devnet_spend reaches the 96-byte generate()
entropy API, not the proof-account route's generate_for_mask_nonce: the candidate predates the
proof-account client route merged into research (D162 route; client-pins.json), consistent with its 6
missing and 26 differing pinned files. V373 stays OPEN (transitive classification incomplete). V374 plan
preregistered (dudect classes, inputs, sample counts, 90-minute kernel windows and a separate four-hour
attempt window): NOT scheduled until the owner fixes the release recipe and the candidate carries the
client route. Launched pv-rebase3 (`codex/pv-rebase3-20261027`, candidate sibling in the reused pv-l3
worktree; IDs 52700-52999): merge research (1,907 commits past the candidate's merge base 970912bfe7)
under the D209 conflict rules (candidate wins inside prover-rewrite files, research elsewhere,
undecidable hunks stop), port devnet_spend onto the proof-account route with call-graph evidence, ELF
pins, the recommended-recipe build and the fixture-byte gate, and the re-validation list of candidate
proofs touched by the merge. Six slots: op223, op134, route2, cblib4, runjoin15, rebase3. Rows removed
outright: 0. Privacy target not yet established.
