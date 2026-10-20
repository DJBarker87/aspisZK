# Final R1 binary privacy composition — 2026-10-20

Branch `codex/cx-priv-final-20261020`, base `1ba1336ac`.
Frozen verifier: `b2727acd3`, as required by
`docs/research/100bit-spend-path-20261013/design/LEAD-FREEZE-20261020.md`.
No existing Lean module or verifier source is edited.

## Theorem in words and exact scope

`R1Z.PrivacyR1Final.privacy_R1_final` is one **conditional** endpoint:
for every witness with the stated public statement, every Boolean observer
of the supplied source experiments has distinguishing advantage against
`simE` at most the binary model error plus the query-scan charge. It also
proves the deployed numerical bound on that same expression.

The real and ideal source experiments are explicit parameters, not an
asserted Rust instance. Two `ScanCoupling` certificates identify them with
the binary model off query-exhaustion events. The real certificate carries
the builder/checker/retry/publication correspondence; the ideal certificate
carries the Rust simulator/programmed-oracle correspondence. Neither
certificate is constructed for Rust here. Thus this is the final composed
privacy **statement**, not unconditional deployed privacy or a source-closure
claim. D75 checker inputs remain open inside that operational handoff.

The mathematical chain is D42 (`privacy_R1`) → D52's phase-indexed
`privacy_R1_games'` → D77 binary games and D78 explicit `simE` → this source
wrapper. The existing `privacy_R1_eff_binary` is imported and axiom-audited;
the new proof uses the unrounded `privacy_R1_games'` expression so every
error term survives. D76's numeric theorem is applied after that composition.

## Error ledger

Write `P = docs/research/v8-r0-zk-20261009/lean/` and
`S = docs/research/100bit-spend-path-20261013/lean/` below. Citations refer
to actual definitions in this branch.

N=8, q≤2^64, E₁≤90112, E₂≤8192, L₁≤45056, L₂≤4096.
`n1_worst_case` gives 2,457,717 reads per attempt, including both binding
reads (P`R1Z/LayoutCountR1PBin.lean:20`); M=19,661,736≤2^25.
`deployed_exact_error` checks the exact-count expression at these parameters;
`deployed_term_values` checks the conservative power-of-two envelope.
`numeric-error.json` contains exact rational numerators/denominators;
floating approximations are display-only arithmetic evidence.

| Slot | Exact expression | Worst-count size | Checked envelope |
|---|---|---:|---|
| adversary hit | M·q/2^255 | 2^-166.7711 | ≤2^-166 |
| prover collision | M²/2^255 | 2^-206.5422 | ≤2^-205 |
| mask word exhaustion | 8·16·(L₁+L₂)/2^496 | 3·2^-475 ≈2^-473.4150 | ≤2^-473 |
| frozen/public-digest hit inside εexh | M/2^255 | 2^-230.7711 | ≤2^-230 |
| ideal programming | Mi²/2^255, Mi=0 | 0 | 0 |
| LogUp pole | 8·4096/((2^31−1)^4−1) | ≈2^-108.9999999973 | ≤2^-109+2^-138+2^-160 |
| real query scan, all 8 attempts | 8·2^-486 | 2^-483 | ≤2^-455 |
| simulator query scan, all 8 attempts | 8·2^-486 | 2^-483 | ≤2^-455 |
| combined query charge | 16·2^-486 | 2^-482 | ≤2^-454 |

εexh is the sum of the mask-exhaustion and frozen-address slots, bounded
by 2^-229 (P`R1Z/PrivacyBoundR1PBin.lean:18`); neither is the query event.
The exact model expression is P`R1Z/PrivacyR1PBin.lean:77`;
D76/D77 aggregation is P`R1Z/LayoutCountR1PBin.lean:34` and
P`R1Z/ReadBudgetR1.lean:60`. The new theorem proves:

```
M q/2^255 + (M²/2^255 + εexh) + 0
+ 8·4096/((2^31−1)^4−1) + 16/2^486
≤ 2^-109 + 2^-137 + 2^-454 ≈ 1.54074396·10^-33.
```

The pole dominates. Its denominator is **p⁴−1**, not p⁴; rounding it
downward to exactly 2^-109 would be false.

The earlier QueryScan bound is per scan (S`QueryScanExhaustion.lean:73`).
Unioning it gives 2^-451 on each side, insufficient for a combined ≤2^-454.
The new lemma uses the same counting inequality
(S`QueryScanExhaustion.lean:66`) and `21^4≤2^18`:
`(2^18)^21·21^64/(2^18)^64 ≤ 2^666/2^1152 = 2^-486`.
Sixteen scan opportunities cost 2^-482. No independence between events is
needed; each actual-history marginal must satisfy its stated bound.
Arbitrary/all-zero query blocks do not satisfy that hypothesis.

## Privacy definition of done

An open entry disappears only when its exact quantified source statement
has evidence against the adopted freeze. The theorem does not assert a
Rust instance of arbitrary W, Pr, h or source. It is a conditional endpoint.

### Accepted premises and proved model components

- **Algebra/public domain:** finite decidable field K with the M31 algebra,
  subfield F, PackBasis/PackField, PublicBase F x.1, and the adopted honest
  relation (P`R1Z/PrivacyR1PBin.lean:54`). N=8 and q≤2^64 delimit the claim.
- **Classical ROM:** finite uniform byte-answer tables and classical observers
  are modelling assumptions. The hash-as-ROM interpretation is accepted,
  not a theorem about SHA-256 or QROM. A concrete RomModel instance still
  needs carrier/lookup correspondence as listed below.
- **Builder model, D46/D51:** BuilderSoundOn is ∀w with h.public w=x.1,
  HonestBuilderSound ... (h.build w) (P`R0Z/HonestValidity.lean:151`). Its
  fields are baseTyped, lanes, helperSum, helperInactive (`:126`). The model
  instance is proved at P`R0Z/BuilderModelRefines.lean:57,66`; identifying the
  deployed trace remains open.
- **Sem1Uniform reduction:** SemRows01, an injective QM31 embedding and
  equality with s1Spend imply the sampler law
  (P`R1J/PrivacySamplerSpend.lean:25`) and sem1Uniform_abR1
  (P`R1Z/Sem1UniformR1.lean:112`). No new abstract Sem1Uniform axiom is used.
- **Binary layout/simulator, D77/D78:** ROpen has two normalized transaction
  batches (P`R1Z/EventsR1PBin.lean:54`); simE has its binary log bridge
  (P`R1Z/SimulatorLogR1PBin.lean:22,36,75`) and bounded model root
  (P`R1Z/PrivacySimulatorBin.lean:19`). These do not prove Rust refinement
  or a new polynomial bit-complexity bound.
- **Shared grammar and separation, D79/D81:** the node/leaf/wire-table
  equality bridges are P`R1Z/SharedGrammarBridgeBin.lean:15,21,25,27,40`
  to S`SharedBinaryRecordGrammar.lean`. Concrete transcript separation is
  P`R1Z/WireLengthsR1PBin.lean:60,65`; the three added classes are
  P`R1Z/WireBindingLengthsR1PBin.lean:14,42`. The final module exports
  shared_wire_separation by rewriting D81's node equality, including compact
  proof 57,607, ASF8 1,880 and checksum input 1,758. This subsidiary layout
  theorem is separate from the privacy inequality, which uses the unchanged
  binary API. Execution membership is still open; arbitrary untyped byte
  lists retain the known overlap, and nodes are not separated from nodes.
- **Query counting:** the independent-word counting bound and its sharper
  consequence above are proved. Transport to source histories is open.

### Open obligations: exact top-level source interfaces

| Final theorem premise | Remaining fact |
|---|---|
| builder_refinement_D46_D51 | Identify the deployed honest relation/public mapping/π and actual builder with h.build; supply all four BuilderSoundOn fields, including D50's change sentinel on the deployed witness relation. |
| D, ι, hι, R_wire_Sem1Uniform | SemRows01.sem1 and sem0 on every answer vector (P`R1Z/Sem1UniformR1.lean:38`), injective field/carrier transport, D.s1=s1Spend ι. Source sampler correspondence includes scalar/circle transport, reseed/nonzero-γ and selected query advance. |
| R_rom_classical | RomModel's full finite address/table equivalence and lookup law on the chosen W (P`R1Z/CouplingR1PBin.lean:115`); source backend matches the common logged oracle. |
| R_rom_address_domain | RAddrIn for every w/sec/d/answer-vector/position (P`R1Z/CouplingR1PBin.lean:169`), including complete read coverage, not just successful traces. |
| R_rom_adversary_budget and observer map | qmax≤2^64 and observer-map preservation; R10/R19 designated first-read accounting through both transactions, backend and normalization, including checkpoint/resume hashes outside opening-only comLog. |
| R_causal_D80 | D80 Earlier form of RCausal at all counterfactual answer vectors (P`R1Z/CausalPremisesR1PBin.lean:19,23`): instantiate Pr.ord, children before parents/roots, row-2 C2 and row-30 folded absorbs after roots; prove all tape/leafVal/outputs/challenge and secret-record dependencies. Root AddressAt plus child-predecessor facts suffice for its root component (`:45`). Successful-cut word stability under collision exclusion is weaker. |
| R_commit_D80.roots/nodes | AddressAt for all three roots/internal binary parents, child order, padded folded geometry, byte carrier and D81 grammar. Do not substitute eight-way C2 recovery for binary recovery. |
| R_commit_D80.leaves | Exact 0x71/0xf1/0x72 tags, packed leafVal/trailing salt, private-leaf backend and byte/digest conversions, on the actual prover tree. |
| R_commit_D80.bindings | Both secret-attempt binding reads, source/public/variant mapping, context encoding and digest answers (P`R1Z/LayoutR1PBin.lean:133`). |
| R_commit_D80.seeds | All three seed derivations, reserved secret distribution and source/D stream selection (P`R1Z/LayoutR1PBin.lean:136`). |
| R_commit_D80.salts | Full per-leaf secret salt derivation, nonce/tree/secret binding and LE32(u) (P`R1Z/LayoutR1PBin.lean:140`); verifier facts only consume disclosed salts. |
| R_commit_D80.mask_expander/source_expander | Stream/domain/seed/LE64(counter), eight words per block, no counter reuse, index/stream selection and complete hash-read coverage (P`R1Z/LayoutR1PBin.lean:131`). |
| R_commit_equal_fibres, cF | Exact equal-cardinality successful tape fibres for every τ. Deterministic expansion and successful tests do not establish uniform tapes. |
| R_commit_exhaustion | Every tapeOf failure implies one of the actual two 16-try little-endian stream-exhaustion events; exact source wordsE transport (P`R1Z/FinalR1PBin.lean:44,54`). |
| R_commit_counter₁/₂, R_commit_stream₁/₂, R_commit_cell_count, R_commit_blocks₁/₂ | E≤2^64, 16L≤8E, RCommitCount cell bounds and E≤2L; universal source commitment read completeness. D76's fixture count alone is not this universal refinement. |
| R_wire_coin_carrier | W.Cm≃(RIdx→OracleAnswer) on all vectors, both inverse laws; three typed roots or a compact proof alone do not construct it. |
| R_wire_D80_batches | Concatenation, per-batch Nodup, exact openedQ membership, fibre union; source sort/dedup/18-level array and padding simulation, normalized source positions, address/answer/first-read preservation. Raw repeated leaf calls are not these lists (P`R1Z/PremisesR1PBin.lean:104`). |
| R_wire_D80_ordered_log | D80 equality of complete ordered byte/answer lists, every w/sec/d/tape/roots/rest/ch (P`R1Z/PremisesR1PBin.lean:62`); set equality is insufficient. commit_source plus this equality derives RComLog. |
| R-wire typed record membership (within address/log/causal/source handoffs) | Instantiate W.frame/payload/final/pubBytes with D79/D81 typed encodings and all three addendum classes; fixed deployed caller lengths and compact expansion. D79 separation is not execution membership; the raw public-slice API remains unrestricted. |
| R_wire_builder_checker_D75_retry | A ScanCoupling for each observer and valid witness between source real and binary real. This includes builder/public/trace identification, all D75.4 checker inputs below, P_chk→P_R1, source acceptance/retry semantics, no_pole↔VR1 on the actual trace, fresh-secret/nonce law, exhausted failView publication, R-ser/R-retry/R-pub and mask/build/salt Semantic errors impossible or observationally accounted for off query scan. D73/D74 tests/readings do not prove this certificate. |
| G_sim_R_wire | Coupling source simulator with simE and its programmed oracle: witness-free input, P-only loop, shifted payloads, exact transcript/commitment/programming logs, source tape law and output/failure serialization. Only query exhaustion may cause disagreement. D78 simulations are not a formal certificate. |
| both couplings: R_rom_query_word_history | Each of ≤8 opportunities has actual scan-event mass ≤ probability (2^18) 64 21. Prove concrete first-stop driver/library correspondence, little-endian low-18-bit distribution, fresh/adaptive shared-oracle history/address transport and prior-read/collision accounting. Neither arbitrary B.decode nor ROM alone suffices. |
| both couplings: R_wire_agreement_off_queryScan | Whole Boolean observations agree off the union of those events, including failure/publication. Source QueryScan aborts the invocation; model kstarOf is total (P`R1Z/GamesR1.lean:82`). Charge real and ideal separately, including unpublished attempts. |

The operational couplings deliberately package the detailed checker/builder
source refinements. No uninstantiated check_sound_cols application is
asserted: its arguments must first be tied to the source attempt. The new
lemma composes the coupling once supplied; it does not prove that an arbitrary
source experiment satisfies it, or infer agreement merely from P_chk→P_R1.

D80 is consumed through AddressAt/commit_bytes_iff
(P`R1Z/PremisesR1PBin.lean:19,29`), com_log_iff (`:62`), causal_iff and
open_of_batches (P`R1Z/CausalPremisesR1PBin.lean:23,73`). All quantifiers are
retained, including inconsistent answer vectors. The shared grammar removes
definition duplication; R-wire/R12/R13, R10 and R15/R19 execution joins stay
open. In particular the frozen-source extraction blockers recorded in the
lead note's addenda are not resolved by this job; no candidate freeze is
adopted.

### D75.4 checker subpremises: complete named input list

The actual endpoint is CertCheckSound.check_sound_cols,
P`R1Z/CertCheckSoundCols.lean:36`, conclusion P_R1 at `:125`.
All of the following remain to instantiate inside the real source handoff:

- Successful checker and decoding (`:36–41`): hc, hup, hnq, hrw; identify
  raw, π, B/hB, w, φ and certificate data with the attempt.
- Tower/chain (`:43–47`): hT, hal, ha9, hbuild.
- Folded targets/widths (`:49–60`): hcov, hbw, hnl, hsel1, hlw1,
  hselH, hlwH; use the actual selection descriptors.
- Lift tables/run (`:62–77`): hnqU, hzx, hzy, htr (π), hin (inact),
  hsx/hsy (stored/OOD points), hselC, hselHv, hloC, hloH, hblo.
- Own-column inputs/runs (`:79–93`): hnU, hosU, hos, hbo, hrow, hlimbB,
  hlane, hwl, hgnU, hgwU, hgw, hbg, hgk, hselG, hgrow, hglane, hgwl.
- WideExact/relation (`:95–115`): hW, hwb, hnfU, hqU, hbr, hti (inverse
  π/ti), hop (opening/OOD limbs), hfp, hinj, hru, hrq, hl0/hl1/hl2 (li), hx16.
- Column writers/x18 (`:118–124`): hbr5, hbg5, hx18, hfo, hbg6. D75
  discharges former entrywise hRent/hGent/hGBent hypotheses through writers;
  those are not additional open premises to reintroduce.

This includes builder-input premises inherited from check_sound''''.
Instantiate every slice, descriptor, basis, index and length consistently.
A proof for another CertData or model trace does not certify the published
source attempt. Checker soundness alone does not supply the full retry-game
coupling, source mask/tape law or failure equivalence.

## Verification

Only new modules are changed. QueryScanExhaustion was installed byte-identical
from this worktree into J because it was absent there. No pre-existing shared
source/olean was overwritten; revisions of this job's own new modules were
snapshotted under the branch name. No frozen verifier, wallet, account or key
was modified. No full frozen-manifest, Rust/SBF or runtime regression was run:
this is additive proof composition, and the covered runtime source is unchanged.

Final declarations (P`R1Z/PrivacyR1Final.lean`): commit_source `:34`,
wire_batches `:50`, shared_wire_separation `:56`, deployed_term_values `:74`,
deployed_exact_error `:90`, privacy_R1_final `:106`.
The new scan lemmas and precise source interface are
P`R1Z/QueryScanPrivacyFinal.lean:15,35,43,71`. Every new theorem has a
#print axioms audit.

| Accepted target | Env J attempt | Exit | Wall | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|---:|
| QueryScanExhaustion (unchanged prerequisite, newly installed in J) | 8000 | 0 | 1.98 s | 3,242,276 | 0 |
| R1Z.QueryScanPrivacyFinal | 8004 | 0 | 1.93 s | 3,521,196 | 0 |
| R1Z.PrivacyR1Final (exact parameters + composition + axioms) | 8008 | 0 | 2.90 s | 4,072,132 | 0 |

Nine new theorems; all final audits use only propext, Classical.choice,
Quot.sound. The final module also audits the imported privacy_R1_eff_binary.
No new options, axioms or admitted proofs. Attempts 8001–8003 and 8005
were elaboration/proof drafts (namespace, symbolic power rewrite, zero-cast,
triangle-algebra fixes); 8006 was a green predecessor. Adding the exact
parameter equality justified 8007; it failed only on an extra tactic after
norm_num had closed the goal, removed for 8008. Failed logs may contain
sorryAx from Lean's error recovery and are excluded from accepted evidence.
No memory failure or unchanged retry occurred. A symbolic exponent-threshold
warning at a ring normalization is retained; no threshold was raised and
no recurrence or large finite universe was evaluated.

Receipts: `attempts.jsonl` and
`docs/research/100bit-spend-path-20261013/evidence/priv-final-20261020/`.
The latter contains manifest.json (focused-extractor-proof-packet-v1),
per-attempt complete output/time/axiom/error JSON, source-pins.json and
audit.json. Source revision is 1ba1336ac with dirty additive sources pinned
by SHA256; objects are represented only by hashes/sizes. `collect.py`
rechecks those hashes, direct-import fingerprints and existing-source
identity without running Lean. It also records exact compiler/launcher/env.

All compiles used the existing run-joint.sh, env J, Lean 4.32.0,
-j1 -M7000 -DElab.async=false, systemd MemoryHigh=5G, MemoryMax=7G,
MemorySwapMax=0, TasksMax=128, launcher reservation check/global lock.
The local soundness-tree workflow was not used. No source/obligation is
claimed closed solely because its name appears in the final statement.
