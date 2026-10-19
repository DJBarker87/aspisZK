# R1 privacy read budget under the binary-multiproof format

Branch `codex/r1p-readbudget-20261019`, base 931d81273. Scope: the
commitment-phase read count Mc and the read budget `115 + Mc ≤ 2^k` of
`R1Z/CommitReadsR1.lean` (`mc_le`), for the compact binary-multiproof format
adopted in `design/PREREG-PROOF-SIZE-2-20261019.md`. The commitment grammar
(`RCommitBytes`), the simulator layout and `GamesR1P` are out of scope
(PROOF-SIZE-OBLIGATIONS items 5–6); §6 lists what in them is eight-way.

## 1. Source count (binary prototype)

The count is of distinct oracle addresses read by one attempt in the
commitment phase (a repeated call at the same address is one read: the
Lean model memoizes it, LOG D52.3). Paths are under
`crates/aspis-r1-cost-probe/src/` unless stated; the binary path is
`prove_masked_attempt_candidate` (prover.rs:163) →
`prove_masked_with_attempt(…, binary = true)` (prover.rs:177).

| Class | Count per attempt | Source |
|---|---|---|
| leaf salts, C1 and C2 | 2 · 2^18 | prover.rs:215 `derive_private_salts` (loop prover.rs:259–261) → aspis-prover/src/state_only_entropy.rs:568 `derive_pool_v1_leaf_salt` (one `LEAF_SALT_DOMAIN` hash per index; the attempt binding it recomputes at :577 is one memoized address) |
| leaf salts, folded | 2^18 | prover.rs:549 (tag 0x72) |
| leaves, C1 and C2 | 2 · 2^18 | host_commitment.rs:213–231, `private_leaf_hash` (aspis-core/src/state_only_private_merkle.rs:46, grammar `0x10 ‖ tag ‖ value ‖ salt`) |
| leaves, folded | 2^18 (values beyond 2^16 are the zero word) | prover.rs:550–554 |
| binary parents, three trees | 3 · (2^18 − 1) = 786,429, roots included | multiproof.rs:221–223 (`BinaryTree::new`: 18 levels, `2^(17−d)` parents at depth d, node grammar `0x12 ‖ left ‖ right`, multiproof.rs:49–51); called from host_commitment.rs:244 (C1, C2) and prover.rs:555 (folded) |
| secret seeds | 3 (mask seed, source-mask seed, D seed) | aspis-prover/src/state_only_hiding.rs:398, state_only_entropy.rs:426, :650 |
| expander blocks | E₁ + E₂ | state_only_hiding.rs:343 (`MASK_EXPAND_DOMAIN ‖ seed ‖ counter`), state_only_entropy.rs:647 (Profile21 D stream) |

Calls that are not new commitment reads:
- multiproof generation (`BinaryTree::multiproof`, multiproof.rs:233; `generate`,
  multiproof.rs:180–206) reads stored digests and makes **no hash call**; the
  compact encoder (compact.rs) makes none either; openings
  (`fill_opening`, `opening_salt`, host_commitment.rs:272, :289) are copies.
- the verifier's multiproof recomputation (multiproof.rs:116–176,
  candidate.rs:92–144) is on the verifier/opening log, not a prover read.
- the transcript (115 reads, unchanged: `t.scalar`/`t.queries`
  prover.rs:538–562 run the shipped message bytes), the statement digest
  `H(public_bytes)` (prover.rs:172; the frozen address) and the two binding
  reads (prover.rs:173 and state_only_entropy.rs:854) are counted as in
  the eight-way model (TRead; the binding reads are positions of `RIdx` in
  GamesR1P and are not in `CRead`).

Total, in the `CRead` convention of CommitReadsR1 (salts, leaves, all tree
nodes with roots, three seeds, expander blocks):

    Mc_bin = 3·2^18 + 3·2^18 + 3·(2^18 − 1) + 3 + E₁ + E₂
           = 786,432 + 786,432 + 786,429 + 3 + E₁ + E₂
           = 2,359,296 + E₁ + E₂.

With the worst-case block budgets of `RCommitCount` (`E_s = 2 L_s`,
L₁ ≤ 45,056, L₂ = 4,096; `blocks_le`): E₁ + E₂ ≤ 98,304, so

    115 + Mc_bin ≤ 115 + 2,359,296 + 98,304 = 2,457,715 > 2^21 = 2,097,152,
                                                      ≤ 2^22 = 4,194,304.

The expander and seed terms do not depend on the tree shape: the mask
material is built by the same `reserve_and_build_…` call (prover.rs:188)
on both paths.

Observation (not in scope, for the lead): the retry loop
`prove_masked_retrying_with` (prover.rs:423–434) calls the eight-way
`prove_masked_attempt`, not the candidate; the binary retry path is a
separate item (PREREG-PROOF-SIZE-2 "retry path").

## 2. Comparison with the eight-way count; which constants depend on Mc

| Term | eight-way (shipped) | binary (candidate) |
|---|---|---|
| salts | 3·2^18 = 786,432 | 786,432 |
| leaves | 3·2^18 = 786,432 | 786,432 |
| nodes incl. roots | 3·(8^6−1)/7 = 3·37,449 = 112,347 | 3·(2^18−1) = 786,429 |
| seeds | 3 | 3 |
| fixed part of Mc | **1,685,214** | **2,359,296** (+674,082) |
| worst expander blocks | 98,304 | 98,304 |
| 115 + Mc (worst) | 1,783,633 ≤ 2^21 | 2,457,715 ≤ 2^22, > 2^21 |
| per-attempt budget | 2^21 | 2^22 |
| M = N·2^k at N = 8 | 2^24 | 2^25 |

In GamesR1P's convention (`n1 = |Pos1| = 115 + |CPos|`, CPos = 3 roots +
E₁ + E₂ + 2 binding + 3 seeds + salts + leaves + non-root nodes) the fixed
part is 1,685,216 (eight-way) and would be 2,359,298 (binary, after the
GamesR1P rewrite of item 6); the worst n1 is 1,783,635 → 2,457,717,
also ≤ 2^22.

Which privacy constants depend on Mc (D41.4/D42.1/D52.1 error
`M·q/Umin + (M²/Umin + εexh) + Mi²/Umin + N·4096/Q`):
- **M** (prover reads charged across all attempts, `M = N·(115 + Mc)` in
  GamesR1/PrivacyGamesR1, `M = N·n1` in GamesR1P/FinalR1P): linear in Mc.
- the **hit** term `M·q/Umin`: linear in M.
- the **collision** term `M²/Umin` and the frozen-digest part
  `M/2^255` of `εexhP` (FinalR1P.lean:68): quadratic / linear in M.
- the **prog** term `Mi²/Umin`: Mi is the ideal side's read count; in
  `privacy_R1_games′` / `privacy_R1_games_spendSampler` it is 0 (the
  simulator's roots are coins), so it does not move; in the D41/D42 form
  (`zkfs_R1_abort_N8`) it was set to M and moves with it.
- the mask-exhaustion part `N·16(L₁+L₂)/2^496` of εexh: independent of the
  tree shape (it counts limbs, not reads).
- the **pole** term `N·4096/Q`: independent of Mc.
- `Umin = 2^255`, `q = W.qmax`, `Q = p⁴ − 1`: unaffected.

## 3. Instrumented count

`crates/aspis-r1-cost-probe/examples/readbudget_count.rs` (new; release
build, host `systemd-run --scope` MemoryHigh 6G / MemoryMax 8G /
MemorySwapMax 0, `-j 4`; time expected and spent in compilation, the run is
two fixture proofs) wraps `HOST_HASH` in a counting `HashFn`, runs the
deterministic R0 fixture once through `prove_masked_fixture` (eight-way, S2)
and once through `prove_masked_fixture_candidate` (binary), and counts calls
and distinct digests per input class. Output:
`evidence/readbudget-count.json`; time: `evidence/readbudget-count-time.log`
(wall 0:28.88 including the build, peak RSS 498,276 KiB, exit 0).

| Class (first input slice) | eight-way calls / distinct | binary calls / distinct |
|---|---|---|
| leaf salt `private-leaf-salt:v1` | 786,432 / 786,432 | 786,432 / 786,432 |
| leaves `0x10 ‖ 0x71`, `0x10 ‖ 0xf1`, `0x10 ‖ 0x72` | 3 × 262,144 | 3 × 262,144 |
| nodes `0x18` (eight-way) / `0x12` (binary) | 112,347 | **786,429** |
| seeds (mask, source, D) | 3 | 3 |
| expander blocks (mask-expand + profile21) | 2,672 + 512 | 2,672 + 512 |
| attempt binding `pool-v1:private-attempt-binding:v1` | 786,433 / **1** | 786,433 / **1** |
| precommit binding `P3:PRIVATE-ATTEMPT` | 1 | 1 |
| statement digest (1,455-byte public input) | 1 | 1 |
| transcript (2 init domains + 33 absorb + 40 + 40) | 115 | 115 |
| fixture secrets (fixture path only) | 3 | 3 |
| **total distinct** | 1,688,519 | 2,362,601 |

So, on the fixture, the `CRead` count is exactly
`1,685,214 + 3,184` (eight-way) and `2,359,296 + 3,184` (binary), with
measured E₁ + E₂ = 3,184 blocks (the worst-case budget 98,304 is the
`RCommitCount` bound). Total distinct = CRead + 115 transcript + 2 bindings
+ 1 digest + 3 fixture secrets, on both paths: no other hash call occurs in
the commitment phase of either format (D52.4 "completeness of the read
list", on this fixture). The 786,433 calls to the attempt binding are one
address (the salt derivation recomputes it, `derive_pool_v1_leaf_salt`
state_only_entropy.rs:576–577), which is why the read count, not the call
count, is the privacy quantity. Proof sizes: 124,343 (eight-way) and 57,607
(binary) bytes, matching the proof-size report.

## 4. The new budget and the Lean change

The smallest change keeping every statement's shape: the privacy theorems
are already parametric in the read count, so only the source-count module
and the numerals move.

- `privacy_R1` (R1Z/PrivacyR1.lean, ε in `M Mi q Umin Q`), `privacy_R1_games′`
  / `privacy_R1_games_sampler` / `privacy_R1_games_spendSampler` (ε in
  `N·(115 + Mc)`), `privacy_R1P` (R1Z/PrivacyR1P.lean, ε in `N * n1 W Pr`),
  `ModelsVR1` (`M q Umin`): **unchanged**; they hold for every count and
  are instantiated at the new constant.
- `R1Z/CommitReadsR1.lean` (changed): `CRead` now has the binary node index
  `Σ d : Fin 18, Fin (2^(17−d))`; `card_nodes = 262,143`;
  `McR1 E₁ E₂ = 2,359,296 + E₁ + E₂`; `card_CRead`; **`mc_le : RCommitCount
  L₁ L₂ → 115 + McR1 (2L₁) (2L₂) ≤ 2^22`**; `mc_gt_2_21`: at the worst-case
  counts (which satisfy `RCommitCount`) `2^21 < 115 + Mc`, so the old bound
  is false, not just unproved. The eight-way count is kept as `CRead8`,
  `card_nodes8`, `McR1_8`, `card_CRead8`, `mc_le8` (`≤ 2^21`), and
  `McR1_sub : McR1 = McR1_8 + 674,082`. `RCommitCount`, the exhaustion
  lemmas and `mass_exh_R1` are unchanged.
- `R1Z/ReadBudgetR1.lean` (new, imports only CommitReadsR1): the numerals
  of §5.
- Not edited: `R0Z/FsAbortR1.lean` (`r1AttemptReadBound`,
  `r1AttemptReadBound_le`, `r1_error_N8`, `zkfs_R1_abort_N8` at 8·2^21).
  They are D41 design-time instantiations, nothing downstream uses them
  (grep), and FsAbortR1 is imported by ModelsVR1 and hence by every privacy
  root, so editing it would rewrite a widely shared .olean for no change in
  any theorem that is used. `r1AttemptReadBound` is an older, looser count
  (it has `2·2^18/7 + 2^16` node reads) and is superseded by `McR1`; the
  binary D41 numeral is `ReadBudgetR1.r1_error_N8_bin`. The lead may
  retire or rename them at the next consolidation.

## 5. The numeric error

D42.1 / D52.1 form at N = 8, q = 2^64, Umin = 2^255, Q = p⁴ − 1
(p = 2^31 − 1), Mi = 0 (`privacy_R1_games′`), M = N·(115 + Mc) ≤ 8·2^22 =
2^25 (was 2^24). log₂ values computed exactly with Python `Fraction`:

| Term | eight-way (2^21) | binary (2^22) |
|---|---|---|
| hit M·q/Umin | 2^-167 | 2^-166 |
| collision M²/Umin | 2^-207 | 2^-205 |
| εexh = 8·16(L₁+L₂)/2^496 + M/2^255 | ≈ 2^-231 | ≈ 2^-230 (≤ 2^-229 proved) |
| prog Mi²/Umin | 0 | 0 |
| pole 8·4096/(p⁴−1) | 2^-108.9999999973 | 2^-108.9999999973 |
| **total** | 2^-108.9999999973 | **2^-108.9999999973** |
| total − 2^-109 | 2^-137.99999999563 | 2^-137.99999999295 |

The new ε is still ≈ 2^-109: the pole term is unchanged and the read-count
terms move by one (hit) and two (collision) bits, 57 or more bits below it.

Proved in `R1Z/ReadBudgetR1.lean` (attempt 5759):
- `r1_games_error_le (Mc qmax εexh) (115 + Mc ≤ 2^22) (qmax ≤ 2^64)
  (εexh ≤ 2^-229)`: the error expression of `privacy_R1_games_spendSampler`
  (verbatim, with `N = 8` and `(abR1 W N hN).N` read as 8) is
  `≤ 2^-109 + 2^-137`;
- `r1_games_error_RCommitCount`: the same at `Mc = McR1 (2L₁) (2L₂)` under
  `RCommitCount` (through `mc_le`);
- `exh_bin_le`: the body of `FinalR1P.εexhP 8 L₁ L₂ M` with `M ≤ 8·2^22` is
  `≤ 2^-229`;
- `pole_N8`: `8·4096/(p⁴−1) ≤ 2^-109 + 2^-138 + 2^-160`;
- `r1_error_N8_bin`: the D41 three-term form (`zkfs_R1_abort_N8`, M = Mi =
  8·2^22, exhaustion slot 2^-250) is `≤ 2^-165` (was `≤ 2^-166`).

For `privacy_R1P` the read count is `N * n1 W Pr`, a cardinality fixed by
GamesR1P's `Pos1`; it becomes the binary count only after the GamesR1P
rewrite (§6), where `n1 ≤ 2^22` follows from the same arithmetic (worst
2,457,717). `r1_games_error_le` then applies with `115 + Mc := n1`.

## 6. Eight-way shape in RCommitBytes, the layout and GamesR1P (for scoping)

Not edited here (PROOF-SIZE-OBLIGATIONS items 5–6). Everything below
encodes the 8-ary tree and must change for the binary format:

- **GamesR1P.lean:45–53** `NodeIdx := Σ d : Fin 5, Fin (8^(5−d))` (non-root
  8-ary nodes; binary: `Σ d : Fin 17, Fin (2^(17−d))`, 2^18 − 2 per tree),
  used in `RIdx`, hence in `CPos`, `Pos1`, `n1` (the read count M of the
  R1P track) and every `Fin (N * n1 W Pr)` coupling vector
  (CouplingR1P/CouplingR1P2/AgreeR1P/AgreeR1P2). Docstring :11.
- **LayoutR1P.lean** (the address grammar behind `RCommitBytes`):
  `child_bound0` / `child_bound` (:86–98, `8·i + j`), `childQ` (:101,
  `Fin 8` children), `rootChild` (:106, root = 8 level-5 nodes),
  `nodeBytes` (:110, `0x18 ‖ child_0 … child_7`; binary: `0x12 ‖ l ‖ r`);
  `gram` root and node cases (:122, :136), `src` (:142, :149; designated
  field = child 7, binary: child 1), `depS` (:154, :163, `∃ j : Fin 8`),
  `fld`; header docstring :8.
- **LayoutR1P2.lean** (32 references): `nodeIdx_ext`, `qNode_inj`,
  `childQ_cases`, `childQ_ne_bind/seed/salt`, `childQ_eq_leaf/node`,
  `childQ_inj`, `childQ_ne_rootChild`, `rootChild_inj` (all over `Fin 8`
  and `8·i + j`); the separation lemmas `sep_*`, `le64_inj`, `treeTag_inj`
  are shape-independent, but the node-vs-other separation uses the `0x18`
  tag byte and must be redone for `0x12` (the PREREG disjointness
  obligation of `BINARY_NODE_TAG`, multiproof.rs:19–21).
- **LayoutR1P3.lean** (33 references): `rd_rootChild`, `rd_childQ`,
  `fresh_or_sep` (node cases at child 7), `openedQ` (:255–260: an opened
  node is `u / 8^(level+1)`; binary: `u / 2^(level+1)`), `div_pow_succ`
  (:273, base 8), `hidden` (node case).
- **EventsR1P.lean**: `RCommitBytes` (:33) itself is shape-generic (it
  equates `Pr.caddr` with `gram`), but `ROpen` (:40) is via `openedQ`;
  `RComLog` (:50) lists the opening reads, whose number changes (the
  verifier now reads multiproof nodes per batch instead of seven siblings
  per level per query; positions are still the opened fibres' ancestors and
  their siblings, so `openedQ`'s "every node on their paths" has to be
  restated for the binary multiproof's opened set).
- **PrivacyR1P.lean:14** docstring (`nodes 0x18 ‖ 8 children`).
- Not shape-dependent: FinalR1P `blockW`/`wordsE` (`Fin 8`, eight words
  per 32-byte expander block), `ksV` / `ksC` / `kstarOf` (`Fin 8`, the
  transcript's k* selector), GamesR1 (the landed, non-phase-indexed games:
  no tree positions), SimulatorR1 and the ideal side (roots are coins).

## 7. Build evidence

Env J, `run-joint.sh` through `joint-drive-range.py` (the manifest-4 driver
with the attempt range confined to 5757–5799), manifest
`build/manifest-5-readbudget.json` (manifest-4 with CommitReadsR1's sha
replaced and ReadBudgetR1 added), `--only` the four modules below. Caps
unchanged (-M 7000, MemoryMax 7 G). All attempts ran outside the parallel
window under the global lock (21:48–21:50 London). Per-attempt records
(module, attempt, source sha, deps fingerprint, exit, wall, peak RSS, swaps,
every `#print axioms` line, errors): `build/attempts-5757-5761.jsonl`;
summary with .olean hashes: `build/summary.json`.

| Attempt | Module | Exit | Wall | Peak RSS (KiB) | Swaps | Axiom lines |
|---|---|---|---|---|---|---|
| 5757 | R1Z.CommitReadsR1 | 0 | 0:02.50 | 2,484,476 | 0 | 24, standard (subsets of propext, Classical.choice, Quot.sound) |
| 5758 | R1Z.ReadBudgetR1 | 1 | 0:01.85 | 2,447,128 | 0 | failed: `exh_bin_le` unsolved goal (norm_num leaves `2^496`, past its exponent limit) |
| 5759 | R1Z.ReadBudgetR1 | 0 | 0:01.92 | 2,459,936 | 0 | 5, all `[propext, Classical.choice, Quot.sound]` |
| 5760 | R1Z.FinalR1P | 0 | 0:02.47 | 3,629,468 | 0 | 9, standard |
| 5761 | R1Z.PrivacyR1P | 67 (refused) | — | — | — | unchanged rerun refused by the launcher |

Shared-olean note: this branch **replaced the shared source
`aspis-joint-20261019/sources/R1Z/CommitReadsR1.lean`** (old sha
`32e360aa…`, new `2252d377…`) and hence its .olean (`006e934f…` →
`0b1e312f…`). The previous source and the CommitReadsR1, FinalR1P and
PrivacyR1P objects are snapshotted in
`/home/dombarker/project-offloads/codex-r1p-readbudget-20261019/snapshot-pre`
(`snapshot-pre.sha256`). The only manifest module importing CommitReadsR1 is
FinalR1P; it was rebuilt (5760) and its .olean is byte-identical
(`330a5021…`), since it uses only `Word`, `Exhausted` and
`mass_exh_attempts`, which did not change. PrivacyR1P (the only importer of
FinalR1P) therefore has the same deps fingerprint and source, and the
launcher refused it as an unchanged rerun (5761); its existing .olean
(`d1afffd2…`, attempts 5402/5547) stands. No other privacy root
(PrivacyGamesSamplerR1, R1J.PrivacySamplerSpend, CertCheckSound3,
BuilderWitnessMerged, R1J.SpendWitnessMap, R1J.SemRowsSpend) imports
CommitReadsR1, so none is affected.

Sources: no sorry/axiom/admit/native_decide, no new options
(`grep` over both files). The 5758 axiom list shows `sorryAx` only because
the elaborator closes the failed goal with it; 5759 is clean.
