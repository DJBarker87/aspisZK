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
