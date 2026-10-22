# Deployed R1 prover side-channel audit — 2026-10-22

Status: source audit complete; D159 privacy target not yet established. Source baseline
`89013d67f06f2b8bf1ab53339d107e60a7cca556`, branch
`codex/cx-sidechannel-20261022`. No shipped code changes are authorized here.

## Contract and scope

D159 supersedes the D143 exclusion: L1 outcomes/counts/I/O metadata, L2 source
trace, and L3 compiler/hardware behavior are separate obligations. D146 limits
statements to expressible canonical source images; it does not make arbitrary
witnesses canonical. D147–158 environment/collection semantics do not imply
constant-time behavior. E1 uniform successful OS draws and E2 atomic persistent
reservation are retained assumptions, not timing guarantees.

The route is the 64-byte `generate_for_mask_nonce` adapter with a public,
adversary-chosen proof-account nonce, then `prove_masked_retrying_with`, the
masked semantic prover, compact publication, and the z4 P_R1 checker. The
96-byte `generate()` convenience route is not substituted. Private coins and
witnesses must be distinguished: a branch on an independent private coin can
be L1-simulatable but still expose a seed-dependent L2 trace.

## Reading the classifications

**a** = witness-independent by a structural reason, possibly using shared
independent coins/environment; **b** = function only of already public inputs;
**c** = finding involving witness or secret-derived data. Subscripts in prose
separate **c-w** (witness cells), **c-q** (Fiat–Shamir values derived from a
private/witness-bearing prefix), and **c-s** (independent secret seed/coin).
The last is not by itself evidence of a different marginal law for two
witnesses. A public-looking challenge type is not proof that challenges of a
*rejected* attempt were public. Successful-proof challenges can be recomputed
from that proof, but rejected-prefix challenges cannot.

L2 classification concerns source operations, not whether LLVM emits a
branch instruction. Equality/`any`/`all`/`contains` may short-circuit; fixed
outer loops do not make their callees constant-trace. Conversely, `pow` with
a fixed/public exponent is not a secret-exponent loop. Every table entry
below includes inherited field-arithmetic findings F2, when field operands
contain secret data; a fixed traversal claim is only about its traversal.

The receipt `source-inventory.json` enumerates declarations and source
operation sites in the reviewed source slices, with SHA-256 and sizes.
It is a lexical review index, not a compiler call graph or formal coverage
certificate; auxiliary verifier/CLI/test declarations in shared files are
explicitly not evidence of reachability. The tables identify the selected
call families. External `std`, allocator, SHA-256/getrandom and caller code
are boundaries, not silently classified as proved constant time.

## Selected route and function inventory

Names below are within the named file. `probe` =
`crates/aspis-r1-cost-probe/src/`; `prover` = `crates/aspis-prover/src/`;
`core` = `crates/aspis-core/src/`; `statement` =
`crates/aspis-statement/src/`; `z4` =
`docs/research/v8-r0-zk-20261009/z4/`. Line numbers refer to the pinned
baseline, not to historical reports.

### Preparation, masks, and durable state

| File:line and function(s) | L1 classification | L2 classification/reason |
|---|---|---|
| `prover/state_only_entropy.rs:202` `generate_for_mask_nonce` | b: zero public nonce; a: successful OS draw sizes 64, two nonzero tests, capped 16 draws under E1; environment failure is observable | c-s: short-circuit seed equality and draw count F3; no witness is read |
| same:227 `mask_nonce`; core/state_only_hiding.rs:153,175 `pool_v1_pair_forest_v1`, `encode` | b: public nonce, statement digest, fixed fingerprints | b: fixed context layout/copies |
| `probe/prover.rs:105` `prove_masked_attempt` | b: public serialization and binding hashes precede secret derivation | b for context/length; inherited c-w/c-q below |
| `prover/state_only_entropy.rs:392` `reserve_and_build_pool_v1_pair_forest_mask_material_v1`; :453 `PreReservedNonce::reserve` | b: nonce/context validation, reserve before deriving masks; `consumed` invariant a | b: fixed context comparisons and one reservation; c-s mask derivation errors |
| same:886,901,905,921,950,962 `open`, `last_error`, `reservation_path`, `reserve_fallible`, durable `reserve`, `sync_directory` | b + adversarial environment: mkdir/stat, atomic create, three writes 16/32/32 bytes, file sync then directory sync. Partial file retained | b path/hash/hex loop; environment-dependent I/O latency/partial writes/retries. No witness or private seed in path/content; F7 |
| same:541,568,863 `validate_pool_v1_context`, `derive_pool_v1_leaf_salt`, `pool_v1_private_attempt_binding` | b: context/tag/index checks and fixed hash lengths; a: salt buffers have 2^18 entries per tree | b control/index; c-s hash contents (leaf seed), requiring hash timing boundary |
| same:634,703 `derive_pool_v1_zero_factor_d`, forest wrapper | a: 1024 K outputs if sampler succeeds; c-s exhausted errors | b active-mask/dependent-row search, fixed 4096 scalar requests; c-s scalar rejection count F3, arithmetic F2 |
| same:760,780,794,804,813,1256 `Profile21SourceExpander::{new,next_word,m31,qm31,drop}`, `profile21_source_expander_block`; :105 `SensitiveQm31Vec::drop` | a until sampler rejection/exhaustion; fixed hash frame; drop has actual prefix length | c-s 1–16 candidate scalar loops, refill and buffer index depend on prior rejected words; c-s short-circuit propagation through 4 limbs; fixed-size zeroization, or length of initialized prefix |
| `prover/state_only_hiding.rs:156,163,169,184` forest active rows, `first_inactive_row`, balance helpers | a: fixed layout/1024 rows | b masks, dependent row, filters and table shape; c-s arithmetic on random masks |
| same:330,350,361,371,397,1497 `SeedExpander::{new,next_word,m31,qm31}`, entropy seed derivation, `state_only_mask_expander_block` | a marginal witness independence of draw/reject count, c-s seed trace F3 | c-s rejection, refill, word offset, early return; entropy zero guard unreachable after successful adapter, to prove |
| same:438,628 `build_mask_material_for_layout`, forest `_from_entropy_ref` | a/b: registry determines mask-cell counts, active rows and requested outputs; c-s failure prefix | b registry selection, active tests, capacities; c-s sampler trace and arithmetic. Registry is not indexed by a witness cell |
| same:685,771 `apply_mask_material_for_layout`, forest apply wrapper | a/b shape errors; c-w balance checks in caller require valid-input invariant F4 | b free-cell list, column/row indices, inactive-dependent placement; c-w additions/balancing F2 |
| same:248,297 `apply_h1_padding_mask_for_active`, forest H1 wrapper | a/b shape and active-padding invariant on generated material | b mask positions; c-s value checks on padding and c-w H1 arithmetic; zero padding and zero sum need invariants F4 |
| `probe/prover.rs:72,76,189,456` inactive sum helpers, `derive_private_salts`, `derive_private_salt_step` | a/b: active masks and 2^18 salts; mapped allocation/semantic errors | b 1024 sums/2^18 iteration slots, fixed push counts; c-w/c-s arithmetic; error propagation preserves failed-call location |

### Semantic proof, commitments, and publication

| File:line and function(s) | L1 classification | L2 classification/reason |
|---|---|---|
| `probe/prover.rs:119` `prove_masked_with_attempt` | c-w/c-s: audit predicates may abort `Semantic`; honest validity must prove them constant; reservation already persists | b buffer lengths and mask indices; c-w equality/filter count/short-circuit audits F4, inherited F2 |
| `probe/host_semantic.rs:216,45` `build_with_material`, `build_with_helper_mode` | b shape/public-statement checks; c-w canonicality, helper sum, boundary, terminal, equal-circle failures F4 | c-w `any`, `from_le_bytes`, equality on columns; c-q z0==z1 and scalar/point samplers. Fixed row-27 semantic schedule on success |
| same:273,309 `no_pole`, `lean_copy_row_values` | **c-w: pole verdict and early rejection F1**; registry-shape errors a | b registry tuple banks/rows/columns/arity/slots and active masks; `clear &=` visits all active slots (no pole-position early exit); c-w tuple arithmetic and derived equality internals F2 |
| `statement/pool_v1/pair_forest_trace.rs:491–665` tuple constructors/translation, registry builder, `tuple_value`, `copy_weight`, `pool_v1_pair_forest_copy_rows_v1` | a/b structural registry errors; values c-w | b registry `find`, bank/index, slot `position`, append-bit and transfer/withdrawal weights. These weights depend on public append index/variant, **not private membership directions**; tuple contents c-w |
| `statement/logup.rs:75,192` `compress_tagged_tuple`, `build_copy_logup_helper`; forest semantic oracle:171 helper wrapper | c-w pole/imbalance errors; normal helper length a/b | b 16-limb compression and weight-zero skips because weights above public; c-w inverses of chi minus witness tuple, zero/error paths F1/F2. Preceding no-pole guard should rule out zero for every actually inverted slot |
| `probe/host_semantic.rs:31,204` `point_claims`, `extra` | a/b fixed 3×29 claims, 56 D-tail coefficients | b lane and tail indices; c-q sparse interpolation point trace F5; c-w arithmetic |
| `statement/constraints_v4.rs:601,782` `sparse_eq_weights`, `multilinear_evaluate_qm31` | a/b column length; c-q internal allocation shape F5 | **c-q trailing ZERO/ONE suffix controls capacity, loop count and column indices**, F5; arithmetic c-w |
| `probe/host_sumcheck.rs:12,38` `interpolate`, `prove_sumcheck` | c-w `Boundary{round}`/`Terminal`, mapped to `Semantic` by caller F4 | b rounds 0..10, 28 samples, 2^(9-round) assignments, interpolation i/j/degree and fixed nonzero denominators. c-w guard equality/early exits; c-q previous challenges in oracle points; F2/F5 |
| `statement/pool_v1/pair_forest_semantic_terminal.rs:1230,1300,2017,2080` `composition_parts`, `terminal_parts`, `Public::{semantic,transition,public_bytes,terminal_qm31}`; private/withdrawal public converters | b public variant/options, public amount, transition/frontier validation and serialization; actual lengths 1455 transfer, 1427 withdrawal | b public frontier carry loop (`append_carry_level`:109), digest lane selectors and source offsets; fixed selected 3×28 claims; c-w arithmetic in composition, Poseidon/copy/mask kernels. Serializer canonical checks are **public**, not witness leaks |
| `statement/pool_v1/pair_forest_copy_terminal.rs` selectors, pattern/window evaluators, endpoint cache, `link_weight`, `add_binary_weight`, `evaluate_with_selectors`; `state_only_poseidon.rs` projected oracle; `core/state_only_hiding.rs:437–659` selected mask factors/value helpers | a/b public layout/variant/point arities; no extra publication | b fixed tensor expansion and registry/cache key indices; public append-bit/variant weight branches; c-w/c-q arithmetic. `selector_mask_sum_16` bit loop follows static masks. Features `optimized-terminal` select kernels at build time, not by witness |
| `probe/prover.rs:12,18` backend `c1`, `c2` | a/b one C1 before lambda/chi, one C2 after helper; missing salt is invariant failure | b 27/2 column placement and salt take; c-w inherited commitment checks/arithmetic |
| `probe/host_commitment.rs:12,40,63` `EncodingDomain::{new,evaluate,encode}` | a/b fixed domain, 4 channels, length-derived recursion and allocation errors | b public geometry/length/depth indices and recursion; c-w field operations in encoding. No coefficient-value sparse shortcut |
| same:96,125–140 `Word::value`, `PrivateSalts::{new,get,len,drop}` | a/b fixed representation/width/whole salt-buffer drop | b word enum by lane, fixed leaf loop; c-q opening index only after query sampling; volatile writes cover every salt; does not promise clearing all witness copies |
| same:144–277 `Commitment::{new_salted,build,root,multiproof,fill_opening,opening_salt}` | a/b fixed lane/leaf counts; c-w wrong-field error F4 | b lane/time widths; c-w `any` over extra limbs, invariant zero on typed inputs; c-q openings and paths F5; field arithmetic F2 |
| `core/state_only_private_merkle.rs` `private_leaf_hash`, digest variant and node framing; `probe/multiproof.rs:49,233–253` binary parent, `BinaryTree::{new,root,node,multiproof}` | a/b 2^18 leaves, 18 levels; fixed tag/frame widths | b full tree allocation/hash ordering/indices; c-q query-selected lookup/multiproof traversal; hash messages contain hidden witness/masks/salts |
| `probe/prover.rs:25,30,36,208` `round`, `fold`, `encoded`, `prove_from_semantics` | a/b sizes by public S2 geometry; compact proof exactly 57,607 bytes; c-q P_R1/QueryScan failures and abort prefix | b public PERM/tail/lane indices and 1024/256/64 folds; c-w/c-q field ops; c-q query indexing/sort/dedup/node counts and Vec growth F5/F6 |
| `probe/transport.rs` `Variant::{tag,row,coefficients}` (also `rows`, `folds`, `final_len` when shared code uses them) | b fixed S2 | b five-digit permutation is a function of loop j only; no secret-addressed permutation |
| `probe/weights.rs:7,19,20,128,149,163,166,296` `powers`, `kpowers`, `double`, `Weights::{new,raw,scalar_factor,tensor,materialize}` | a/b fixed 7 weight kinds/1024 outputs | b exponent/index/kind/S2 inactive-mask selection and tensor loops; c-q arithmetic. Verifier-only `pair`, grouped-pair and dual helpers are not called by this prover materialization |
| `core/r0/{encoder,basis,domain,fold,heap}.rs` message evaluation, natural basis, fibre geometry, phi inverse and `filled`; `core/r0/mod.rs` CodeField wrappers | a/b lengths and fixed/public basis indices | b basis exponents/coordinate indices and allocation requests; c-w/c-q arithmetic when operating on messages/challenges. `filled` allocation failure is environment, not a witness proof |
| `probe/compact.rs:82,86,109` `compact_row`, `compact_semantic`, `compact_values` | a/b fixed row widths/high-half invariant; c-w invalid-high failure outside invariant F4 | b row loops; c-w high-half `.any` only if invariant not proved; all high halves zero on correctly constructed K messages; no value-dependent compression length |
| `probe/multiproof.rs:54,198` `well_formed`, `generate` | c-q actual node counts internally, fixed padded node-slot output sizes | c-q sibling-sharing loops, queried `node` addresses, `sort`/`dedup` before it F5; `BinaryTree::new` is full/fixed. `verify`, `verify_in_place`, `sort_dedup` are verifier helpers, not called here |

### Transcript, retry controller, checker, and simulator

| File:line and function(s) | L1 classification | L2 classification/reason |
|---|---|---|
| `probe/r1_wire.rs:39–100` `row_shape`, `validate_record_fields`, `parse_record`, `record`, `encode_values` | b rows/framing/widths; c-w invalid-field prefix F4 | b row tags/widths, c-w canonicality and high-half checks until typed-input invariant proved |
| same:179–269 `SemanticTranscript::{new,state,sample_block_validated,sample_block,semantic,challenge_reference_circle_point}`, `statement_points`:382 | a/b fixed absorb/squeeze/advance frame sizes by row | b row-order/row-kind branches; c-q field/circle sampling and field arithmetic. Validated-record/verifier-prefix methods do not bypass the selected prover's raw record validation |
| `probe/transcript.rs:7–86` `Transcript::{new,absorb,block,scalar,scalar_k,queries}` | a/b fixed hash requests on successful schedule; query error aborts | b domain/row/nonzero flag, **all eight query block pairs are hashed even if scan ends early**; c-q QueryScan and sampler trace F5; trace buffer F7 |
| `probe/sampler.rs:8–127` division pass/digits/low digits/decode/add-small, `qm31_sample`, `ordinary_sample`, `gamma_sample`, `circle_sample` | a/b fixed sampler outputs; fallback does not retry | b fixed 8-word/4- or 8-pass loops; c-q integer dividend `/ P`, `% P`, gamma carry branch, circle singular/subfield/fallback branch F2/F5 |
| `core/circle.rs:34,55` secure rational/OOD helpers; transcript circle fallback | a/b deterministic point output including fallback | c-q inverse zero/subfield tests; fixed-index fallback selected by public row; no rejection-sampling loop |
| `core/r0_transcript.rs:186,202,216,305` `query_words`, `QueryScan::{scan,finish}`, `queries_from_pairs` | c-q bounded query-scan exhaustion -> `Transcript` abort (not retried) | c-q duplicate `contains`, accepted index, early stopping and selected advance F5; raw full-core scalar samplers/reduce_rank are not used by the fast probe sampler |
| `probe/prover.rs:172,182,307,354` `mask_error`, `semantic_error`, `public_check`, `prove_masked_retrying_with` | c-w pole; c-s mask exhaustion; c-q P_R1 reject; only `Rejected` retries, all other errors abort; successful attempts field public F1 | loop exits at first success/other error, max 8; callback `next_attempt(k)` receives k; TLS push length follows actual P checks F6/F7 |
| same:301 `take_check_times`; `probe/trace.rs:6,14` `value`, `take` | c-q: check count/phase times and retained challenge values callable by host; no automatic network/disk write | c-q Vec growth by attempt/check schedule F6; fixed-sized trace record, F7 |
| `z4/z9e.rs:50,90,184,196` `public_data`, `extracted_builders`, `install_quiet_hook`, `p_r1_check` | predicate is b **given challenges**, c-q on hidden attempt prefix; phase timers reveal failing phase, caught panic becomes reject | sort/dedup query indices; challenge-derived certificate rank, indexed pivot/selection arrays, allocation sizes; `catch_unwind` phase-dependent early return. Quiet hook suppresses panic text only; F1/F6/F7 |
| `z4/z9c.rs:18–156,208–532` scalar helpers, `TagEch::{new,insert,express}`, kernel coefficients, source/lift/chain helpers, `invert`, `emit` | c-q emitter refusal changes retry count; certificate not sent | c-q zero skips, first pivot search, rank thresholds, break on lift/target completion, row swaps and inverse work; certificate vector lengths depend on ranks, F6. This is not constant work merely because check is verified |
| `z4/z9d.rs:18–359` `flat`, `family`, `image`, `matmul`, `convert` | c-q malformed shape/index returns None -> reject | c-q certificate-sized loops/allocations, indexed sources/pivots, `matmul` zero skip. Data are functions of ch, not separate witness input |
| `z4/z9.rs` R1 `row/coefficients`, geometry/weights/round/fold/evaluate helpers, `Geo`, `Lay`, `Ctx`, `Lanes::{new,count,bal}`; `z9b.rs` line geometry, functionals, `weights_design`, `design_relations`, `Rel::limb_functionals`; `probe.rs` `raw_c`, `raw_c_with_transport`, h/round/tail/eval/point/flatten helpers; `z5.rs` transport selectors | b given ch/public geometry; c-q candidate prefix | b static transport and basis masks; c-q query-layout dedup, field/zero tests, index and dimension computations; inherits F2/F5/F6. Probe CLI main/trial RNGs/rank experiments are not invoked by library entry |
| `c3/build/src/lib.rs` arithmetic, selector/index/source helpers and all `fill_{tq,lo,own,rel,round,gbat}` helper loops | b given ch/cert, c-q before rejected-attempt disclosure | b many fixed-shape loop bodies; c-q descriptor/index/length arguments and `% P` operands. No claim that an extracted arithmetic-correct builder is constant latency |
| `c3/check/src/lib.rs` `dot`, `kdot`, `kimg_ok`, `piv_ok`, `ents_ok`, `prod_row_ok/prod_ok`, `id_row_ok/id_ok`, `ech_row_ok/ech_ok`, permutations, `nvec_row_ok/nvec_ok`, `lifts_ok`, `mm`, `half_ok`, `check_qprime/check_bcond/check` | b given complete checker inputs, c-q actual run | c-q early exits on failed equalities, certificate/pivot/tag indexing and lengths; modular arithmetic operands. Soundness theorem does not certify a fixed trace |
| `probe/sim.rs:79–142` `Coins::{new,coin,nonzero}`, `concat`, `CoinOracle::digest`, `ProgramOne::digest`, `install/uninstall/programmed_hash` | a: no witness argument; c-s simulator seed and hidden programmed coordinates | c-s unbounded nonzero loop; full-byte BTree keys/comparison length, insert/overwrite/collision, get/hit set insert; F6 |
| same:152–350 `Records::placeholder`, `walk`, `tape`, tcheb/nodes/eval recursion/`eval_at/encode_at`, `challenges_of`, `semantic`, `opening` | a given public x and simulator coins; simulator's failure branches differ from real F1/F4 | b fixed public geometry; c-s tape/mask sampling and arithmetic; c-q point/query work as above. Ablations are audit choices, excluded from deployed claim |
| same:358–505 `ProgrammedTree::multiproof`, `program_tree`, `sim_e/sim_e_ablated`, `verify_programmed` | a witness-free implementation, **no proof of same joint L1/L2 law as real** | c-s/c-q full-byte program-table comparisons, query-key maps, lazy entry callback, parents-set iteration; rank/time and buffer sizes differ from real F6 |

Excluded from the deployed route: deterministic fixture APIs, 96-byte
`generate()`/its convenience retry wrapper, test forced-verdict/pole hooks,
old unsalted/eight-way paths, verifier-only dense/pairing routines, and
cfg(kani/aeneas_ref) owned-reference modules. They do not repair the native
trace. The compiler declaration census deliberately retains some shared
helper declarations to make omissions reviewable, not to assert these are
called.

## Findings, severity, and exact attempt laws

### F1 — retry outcomes include a witness-derived pole predicate (priority 0)

At `probe/host_semantic.rs:283–295`, `lean_copy_row_values` reads the
**unmasked compiled witness trace**, compresses its tuple limbs with lambda,
and tests chi against every active static slot value. `clear &=` prevents an
outer early exit, but its verdict controls the `ActivePole` return at
:249. `semantic_error` (`probe/prover.rs:182–188`) maps that to `Rejected`;
:363–369 then retries. Thus changing a tuple value while fixing lambda/chi
can change the rejection decision. Example at the local compression helper:
with tag t, lambda=1, one variable limb v and all other limbs zero, the
value is t+v. Chi=t rejects v=0 but not v=1 (unless another slot also has
that chi). The secret is the compressed tuple data, including private
membership/path/note-derived cells. This is a concrete local distinguishing
predicate, **not a constructed pair of valid spends with identical public
statement**. No such full pair was produced in this audit.

Let Q=P^4, L=2^256, h=floor(L/Q), d=L mod Q. For a fixed witness w and
lambda, let S_w(lambda) be the **distinct** K values at all copy-active
static slots (including unused zero slots, as this implementation does).
On a fresh independent uniform raw row-1 block, the **exact** conditional
pole probability is

```
Pr[pole | w,lambda,fresh independent row-1 block]
 = (h*|S_w(lambda)| + #{s in S_w(lambda): rank_K(s)<d}) / L.
```

This includes the modulo sampler bias; replacing it by |S|/Q is not exact.
The existing bound |S|≤4096 gives an upper bound, not equality of laws
between witnesses. The two-tuple check in `checks.json` shows why fixed
slot counts alone do not fix distinct-value cardinality. It is deliberately
labelled a local obstruction, not a forest-registry counterexample. Under
ROM memo hits/adaptive conditioning, freshness is itself an obligation; E1
alone does not give the displayed conditional law for hashed challenges.
P_R1 depends on later challenges too, so multiplying a pole-free fraction
by an independent P_R1 acceptance fraction is unjustified.

P_R1 itself has **no direct witness read**: `z4/z9e.rs:50–82,196–221`
constructs all its inputs from `R1PublicChallenges`, emits a certificate,
builds/checks it, catches panic, and returns one bit plus durations.
It even ignores the supplied C1 root in `probe/prover.rs:314`. Its actual
challenges do depend on commitments, helper values and sumcheck messages
of the private run. Consequently “checks public data only” proves
functional factoring through ch, **not witness-independent attempt law**.
Emitter false negatives, `HalfOK` failure (`z9c.rs:336–343`), rank failures,
and caught panics are all part of the enforced predicate P_chk.

The real outer control has outcomes R (exactly `Rejected`), S (success),
and E_e (other error e); it also has callback error E before proving. Let
C_k be the event that the first k-1 iterations returned R. For 1≤k≤8:

```
Pr[success at k] = Pr[C_k] * Pr[S_k | C_k]
Pr[abort e at k] = Pr[C_k] * Pr[E_{e,k} | C_k]
Pr[AttemptsExhausted] = Pr[R_1 ∧ ... ∧ R_8].
Pr[iteration k is entered] = Pr[C_k].
```

These identities, with hazards depending on public inputs, prior oracle
history, the ledger/environment schedule and w, are the exact law justified
by source. The observable record must additionally locate callback versus
reservation, derivation, semantic, query-scan, checker or publication failure.
For genuinely iid, stationary, error-free attempts with acceptance a_w,
they simplify to a_w(1-a_w)^(k-1), with exhaustion (1-a_w)^8. Conditional
on eventual success the former is divided by 1-(1-a_w)^8. Source does
**not** establish those iid hypotheses: nonce choice, duplicate ledger
entries, faults and retained ROM history are allowed to be adaptive.
There is no justified single numerical geometric parameter for deployed R1.

Further terminal branches are **not retries**: equal circle points become
`Semantic`; QueryScan exhaustion becomes `Transcript`; entropy error aborts
through the callback. Mask scalar exhaustion alone is mapped by
`mask_error` to R. Ignoring these creates the wrong count distribution.

**Recommendation:** first extend the existing coupling to the entire L1
record and retain rejected prefixes. Outside the pole/exhaustion/memo bad
events it may preserve attempt counts exactly; prove this and charge the
existing pole term once, including abort labels. This is proof work and can
establish approximate joint privacy, but cannot be advertised as exact
witness-independent acceptance. If exact independence is required, redesign
pole handling/selection or use fixed work and a proved witness-independent
success/failure law. Performing eight attempts alone does not hide whether
all fail, nor repair secret work inside an attempt. That changes the frozen
prover/protocol execution and requires adoption gates. No patch made.

### F2 — canonical field operations have data-dependent source branches (priority 0)

`core/field.rs:32–45` reduces with `if x>=P`; M31 add :61–90 and
subtract :98–125 conditionally subtract P; negate :125–130 tests zero.
For canonical values, `add(0,1)` takes the non-reduction arm while
`add(P-1,1)` takes the reduction arm. `neg(0)` versus `neg(1)` also
separates canonical inputs. These operations are called on witness-bearing
masked trace cells, unmasked tuple compression, sumcheck columns, helper
values and terminal polynomial evaluation. Even fixing an independent
additive mask, translating a witness value changes whether a sum crosses P.
This is a direct failure of a universal equal-source-branch helper theorem;
it is not a measured timing attack and does not claim a full valid-spend
pair has been constructed.

CM31, QM31 and WideExact add/sub/mul/square/dot/packing/prepared
multipliers inherit M31 reduction branches. `QM31::is_zero` (:985),
`try_inv` (:1004), parser `?` chains (:1022), derived aggregate equality,
and `WideExact::from_limbs` (`field/wide_exact.rs:209`) introduce zero,
canonicality and short-circuit paths. QM31/CM31 limb structs can be raw
noncanonical constructors; D146's public-statement domain does not eliminate
all malformed trace inputs. F4 treats which of these paths are reachable.

M31 inversion :213–231 uses a **fixed 38-multiplication addition chain**
after its nonzero assertion. There is no Euclidean variable-trip inversion
here. The nonzero precondition can remove its panic branch, but its field
multiplications remain F2. QM31 inversion uses a norm and lower inversion,
not a secret-exponent search. Generic `pow` loops branch on the exponent;
prover uses fixed/public geometry/sample exponents, so this is b for loop
structure, with c operands inside arithmetic.

`wide_exact.rs:283–295` canonicalizes all four limbs by `% P`;
`mul_m31`:190–198 also uses `% P`. `probe/sampler.rs:8–70,95–103`
uses u64 division/remainder by constant P. `c3/build` uses `% P` throughout
arithmetic. These are variable-latency-operation **operands**, but actual
latency is L3: constant-divisor lowering may remove hardware divides.
No arbitrary-size big-integer or secret Euclidean loop was found in the
selected field path; fixed word arrays are not variable-length bignums.

**Recommendation:** audited fixed-trace field kernels, total constant-work
zero handling and parser strategy, plus relational proofs of their actual
callers. This changes shipped host arithmetic (may preserve protocol bytes
mathematically, but changes the frozen prover and invalidates its source
pins). Proof work alone cannot erase these source `if`s under strict L2.
L3 evidence must follow a new compiler/CPU pin, not justify calling the
current source L2-constant.

### F3 — private-coin nonzero and limb-rejection counts (priority 1)

`generate_for_mask_nonce` tests the public nonce once. Each successful
64-byte OS draw is split into two independent 32-byte seeds and rejected
when **either** is zero (`state_only_entropy.rs:205–224`). It does not choose
the nonce from sixteen candidates; it makes at most sixteen OS calls. Under
E1 and all-Ok OS schedule, let u=2^-256 and s=(1-u)^2. Then

```
Pr[first accepted draw=n] = (1-s)^(n-1)*s, 1≤n≤16
Pr[zero exhaustion] = (1-s)^16 = (2u-u²)^16.
```

This count is independent of witness; it depends on private OS coins, and
`&&` skips the second seed test if the first is zero. OS error at any reached
call exits immediately. With a byte-blind adversarial schedule, use its exact
conditional stopping law, not the all-Ok geometric formula. Successful
seeds are independent uniform **nonzero** blocks under that ideal schedule.

Both `SeedExpander::m31` (`state_only_hiding.rs:361–369`) and
`Profile21SourceExpander::m31` (`state_only_entropy.rs:794–802`) draw
`word & 0x7fffffff`, rejecting only P. Raw words P and 0xffffffff reject;
0 succeeds. Thus explicit streams [0], [P,0], [P repeated 16] respectively
use 1 draw, 2 draws, and exhaust. For independent uniform words, r=2^-31,
Pr[success at j]=r^(j-1)(1-r), and exhaustion r^16=2^-496.
A field request may reuse a ROM block already read: independence of every
word conditional on history is **not** automatic for the hash expander.
This formula is the ideal fresh-word law, not a new source-refinement theorem.

Seeds and mask stream requests depend only on public context and independent
coins, not witness values. Accordingly these counts are class a for marginal
L1 witness independence and c-s for private-coin trace. Disclosure of coin
predicates must still compose with the masked transcript; unconditional
uniform masks are insufficient if leakage conditions their distribution.
`qm31` short-circuits on the first exhausted component, and refills/word
indices become functions of earlier rejection counts. The simulator's
`Coins::nonzero` (`sim.rs:84`) is an **unbounded** zero loop and does not
implement the native capped two-seed draw schedule.

**Recommendation:** proof-only deliverables can couple native seed draws,
mask rejection traces, retained word offsets and the byte-blind fault schedule
with a witness-free simulator, including conditional mask hiding. If strict
all-secret fixed trace is desired, replace bounded rejection/zero sampling by
an adopted constant-work sampler with its exact distribution and failure
law. This changes frozen host behavior and may change the sampler law used
by protocol proofs. Do not silently replace it by reduction modulo P.

### F4 — semantic/canonicality early exits require honest-input refinement (priority 1)

`host_semantic.rs:58–70` scans C1 and D/G for canonicality before
commitment; `Commitment::build` checks high limbs with nested `any`
(`host_commitment.rs:181–188`); raw record validation
(`r1_wire.rs:51–59`) returns the first failing field; compact serialization
checks high halves (`compact.rs:114–117`). On bad raw witness columns,
changing the position of a noncanonical element P changes scan length and
failed-call location. These are genuine helper-level c-w examples, but
malformed values are not automatically members of the honest-spend domain.
On typed canonical K inputs every limb check succeeds, high halves are zero,
and loops have fixed lengths. A proof of those invariants can close these
particular branches without changing code. Correctly classify `Public::fields`
(:2020) separately: it checks public values, hence b even on invalid inputs.

`prover.rs:139–158` balanced-column audit counts/equalities, helper total
sum :158, `host_semantic.rs:99` helper sum,
`host_sumcheck.rs:65,76` boundary/terminal equalities, and `z0==z1`
(:188) all affect early exits. For valid honest traces, algebraic invariants
may make most guards constant; source alone is insufficient. Equal circle
points can arise from the sampler fallback and are not made impossible by
canonicality. No-pole is different: the honest witness need not be pole-free
for every challenge. Do not prove it away as an invalid-input error.

**Recommendation:** proof work only for canonicality, field-width, balance,
shape, nonzero-inverse and honest semantic guards that are invariant; include
the full native caller and all failure statuses. Prove which challenges
admit equal points and its joint abort law; changing their abort into retry
or suppressing errors would change the frozen prover. These proofs do not
close F2's value-dependent arithmetic within successful guards.

### F5 — challenge-derived indices and sparse allocation are not all public (priority 1)

At `constraints_v4.rs:601–627`, `sparse_eq_weights` counts the trailing
ZERO/ONE suffix of its point, allocates `2^prefix_len`, and indexes the
witness column at `(prefix<<trailing_boolean)|suffix`. All-zero point gives
one entry/row 0; replacing only the last coordinate by 2 gives 1024
entries and rows 0..1023. These are canonical point inputs. During sumcheck,
trailing assignment bits are public loop variables, the current coordinate
is the public sample 0..27, and **previous** coordinates are FS challenges.
If a sampled current coordinate is 0 or 1, the suffix test can continue into
previous challenge coordinates. The all-zero-versus-2 example is a local
function witness, not a proof that those full points occur with appreciable
probability or that the two complete spends share x.

QueryScan (`r0_transcript.rs:202–224,305–321`) has duplicate-dependent
`contains`, accepted-array indices and early stop. [0,1,...,21] versus
[0,0,1,...,21] yields the same accepted list but a different source trace;
accepted query list alone therefore cannot reconstruct all duplicate-branch
leakage. The eight pairs are always hashed by `Transcript::queries`, but
scan work and returned state vary. Exhaustion aborts `Transcript` rather
than retrying. Successful query indices and decoded proof are public;
rejected-attempt query indices, duplicate raw candidates and scan prefixes
need the joint leakage law.

`prover.rs:262–279` query indices select word/salt locations, sort/dedup
folded query indices, traverse multiproofs, and pad each node slot. The full
Merkle tree itself is constructed in fixed public order. For indices [0,1]
versus [0,2], level-0 sibling sharing changes emitted node count, internal
work, and output-vector growth before padding. The final node slot length
stays fixed. No witness-cell-as-index was found in the fixed free-cell
registry, transport permutation, normal full encoding or copy registry;
the secret-derived addressing is via FS/sparse point/query values.

**Recommendation:** proof-only L1 transport can condition on successful
published proof indices but must simulate rejected scans and duplicate
history jointly. Literal L2 fixed addressing needs an oblivious/fixed-shape
evaluator and oblivious opening gathering/tree traversal, or a proved
witness-independent law for the *entire* exposed challenge-derived trace
under the adopted definition. Implementing fixed shape changes the frozen
host, even if proof bytes remain identical. Successful proof publicness
alone is not that proof.

### F6 — secret-derived collection cost, ranks, and allocations (priority 1)

The native real `prover.rs` uses Vecs and a full `BinaryTree`, **not a
secret-byte BTree programming table**. BTree concerns in this task are
principally simulator/oracle code, plus query-driven checker layouts. In
`sim.rs:99–118`, both digest adapters insert concatenated oracle inputs
in `BTreeMap<Vec<u8>,[u8;32]>`, compare old answers and set collision flags.
`programmed_hash`:133–142 does full-address get and hit-set insert.
`sim_e_ablated`:439–461 uses query-keyed opened/folded/leaf maps;
`folded.entry(v).or_insert_with` skips evaluation on repeated parents.
`program_tree`:368–388 builds parent sets, map lookups, missing-child coin
callbacks and insertions; its `ProgramOne` calls use keys containing hidden
leaf values/salts or hidden child digests. Key lexicographic prefix, map
occupancy and insertion history govern comparison path/work. E.g. equal
length keys differing at byte 0 versus byte 31 cause different byte-comparison
prefixes in the ordinary documented lexicographic model; actual std machine
implementation is an L3 boundary. Integer keys 0/1 versus 0/4 change parent
sharing. These are c-s/c-q, not direct witness reads by the simulator.
A semantic TrustedStd insert/sort/dedup law from D145–157 contains **no cost
law** and cannot establish L2.

The checker `TagEch::insert/express` (`z9c.rs:108–153`), `invert`:290–319,
`emit`:332–532 and `convert`/`matmul` (`z9d.rs:90–359`) take different
pivot searches, zero skips, row accesses, vector growth and stopping points
for different challenges/certificates. `alpha[9]=1/2` stops immediately at
HalfOK; other alpha may proceed to lift elimination. It does not follow
that both choices are sampler preimages on the same full valid run, but the
checker interface is demonstrably variable-work. Certificate ranks and
chosen pivot count determine allocation/request sizes. Outer fixed dimensions
do not fix these prefixes. The certificate stays local; the four timing
values can expose how far the check got.

Most other sizes are a/b: 16 semantic C1 columns, 10 mask-only columns,
1024 rows, 29 message lanes, 2^18 salts/leaves per tree, 18 tree levels,
3×29 claims, 10×28 sumcheck coefficients and final 64 E elements. Exceptions
are F5 sparse weights, query/multiproof node vectors, failure-prefix buffers,
certificate rank vectors and TLS `CHECK_TIMES`/`VALUES` growth. Allocator
failure behavior and allocator implementation require an environment model;
a fixed requested size alone does not prove equal wall time.

**Recommendation:** keep simulator tables ideal/private only if the adopted
L1/L2 observation projection explicitly permits it and prove the simulation
of the real trace; merely hiding a table's values does not hide its cost.
For actual observable implementation traces, use oblivious fixed-capacity
operations or establish the appropriate conditional trace distribution.
Proof-only semantic collection laws are insufficient. Real checker/rank
padding or replacement, table replacement, or disabling native TLS collection
changes the frozen host, even when certificate soundness is unchanged.

### F7 — persistent effects and instrumentation expose attempt structure (priority 1)

Each successful reservation writes a `.burn` filename that is 64 public
SHA-256 hex characters plus the five-character suffix. It contains exactly
16 magic bytes, 32 statement-digest bytes and 32 public nonce bytes. The
three logical `write_all` requests precede file sync then directory sync
(`state_only_entropy.rs:929–944`); `write_all` can issue shorter writes and
retry according to the OS. `AlreadyExists` stops without writing; a partial
write/fsync error leaves the entry occupied. No witness/seed bytes are
written by this ledger. Across attempts the **number and ordering** of burns
is gated by F1/F3/F4; later call times can reflect prior secret work. The
first reservation is before secret derivation, as D148 requires; subsequent
reservation time is not independent merely for that reason.

The requested library route sends no network request and writes no proof
file; it returns a proof Vec and an audit/attempt count. Successful proof has
57,607 bytes, 22 openings in sampled query order, then six fixed padded
node slots in batch/tree order; internal semantic transcript messages are
buffered before final return. It does not stream rejected proof bytes to the
network. Upload chunk sizes, transaction order, proof-account creation and
funding, cancellation behavior, logging and client-side persistence are
caller obligations absent from this API. Keypairs must be retained while
they control funds/rent/tokens/authority; this audit creates or destroys none.

Contrary to a broad reading of “nothing about it is returned or logged” in
`prover.rs:346–350`, production-feature code retains data about attempts:
`trace::value` (`trace.rs:6–10`) is active with feature `prover`, and
`Transcript::scalar/scalar_k/queries` push values/query records into TLS;
`trace::take` returns them. `public_check` pushes each check's four durations
into TLS (`prover.rs:317–318`), and `take_check_times`:301 returns them.
`RetriedProof.attempts`:323 exposes count directly on success. There is no
automatic disk/network export, but a calling host can retrieve this state,
including some rejected-attempt challenge traces. Unconsumed TLS vectors
can accumulate across multiple proofs, rather than being cleared by the
retry call. Test-only CHALLENGES/forced verdict hooks are separate and not
used as evidence of a production leak.

**Recommendation:** prove the L1 ledger/effect projection under public nonce
and byte-blind faults, then compose with the retry law and the actual client
publication schedule. Document host access to TLS values/timings as part of
the observed record. Removing/gating instrumentation and padding external
schedules changes frozen host execution; source-faithful modeling, retention
of histories, and exact I/O-publicness proofs are proof-only. Do not claim
“no publication” means no side channel.
