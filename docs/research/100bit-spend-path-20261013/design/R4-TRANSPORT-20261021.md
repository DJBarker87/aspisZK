# R4 sampler and prefix transport

Branch `codex/cx-r4-transport-20261021`, base `9b9b652a9`.
Status: **R4_transport remains open**. No boundary premise is removed.

## Stage 1: frozen-path inventory

The source pins and sizes are in `evidence/r4-transport-20261021/source-inventory.json`.
The selected path is S2 (two folds); S1 places queries/rho at 30/31 and is outside this claim.
The latest C3 addendum identifies `R1FinalSoundnessHeadline` as the consolidated endpoint,
which retains `h_R4_transport : s.R4_transport`. R19 is its earlier predecessor.

| Rows | Shipped call | Selected Lean model | Existing evidence / open join |
|---|---|---|---|
| 25,26 | r1_wire circle_validated; sampler circle_sample; secure_ood_circle_point_from_parameter with fixed fallback | SelectedChallengeMap circle views; R0P circleSample0/1 | Extracted wrapper policy and QM31 totality exist; exact point equality, current caller and full prefix still required |
| 27 | Transcript scalar(nonzero=true); sampler gamma_sample | OpeningSamplerBound gammaSample / ModuloField nonzeroRank | Optimized low-base-P quotient folding is not the legacy binary reducer; pinned PreparedModel leaves B.gamma free |
| 28,29,30 | Transcript scalar(nonzero=false); sampler ordinary_sample | OpeningSamplerBound sample / ModuloField fieldRank | Pinned PreparedModel leaves B.ordinary free; serialize inactive and round payloads, including root || round1 |
| 31 | Transcript queries; core queries_from_pairs; QueryScan scan / finish | QuerySamplerBridge, Q22WordScan, SamplerWords | Mask low 18 bits, stable first22, at most64 draws; iterator and selected-state joins remain |
| 32 | Transcript scalar_k; sampler qm31_sample | rhoOf (sigma32 block) = SemSource qm31Sample | Existing extracted sampler arithmetic can be composed with successful block call |

Field input words are **not rejected** when >= P: all 256 bits form one little-endian rank.
QM31 and ordinary reduce modulo P^4 and P^8; gamma reduces modulo P^8-1 then adds1.
Circle mapping uses one parameter and fixed row fallback, not parameter retries.
Row31 rejects duplicate masked candidates, consumes at most eight blocks, and rejects if fewer
than22 distinct indices occur. The stop guard is before each word: filling slot22 on word8
consumes the next block before stopping, except at the eighth block. The returned state is
that selected advance, not unconditionally advance7. All eight pairs are hashed eagerly by
the shipped wrapper even when the selected advance is earlier.

`r0_sample_row` is explicitly provisional and rejects row32; it is **not** the deployed
33-row caller. Legacy Transcript challenge_qm31 rejection sampling is also not this path.
D86 concerns the builder S2 transport, not a proof of all challenge samplers. D88/PHASE2
constructs a protocol model and explicitly retains Rust sampler/parser/execution joins.

## Stage 2: focused sampler work

### Optimized wide-sampler reference

`R4TransportGammaFold` proves the quotient-fold identity symbolically. If
`total = x % modulus + x / modulus + 1`, the optimized integer result is
`total` below modulus and `total - modulus + 1` otherwise. Under the source
quotient bound this is exactly `x % (modulus - 1) + 1`. Equality at modulus
belongs to the carry branch and returns1. No field carrier is enumerated.

`R4TransportGammaRank` specializes to `modulus = 2147483647^8`: every
`x < 2^256` has quotient below257; the rank is strictly positive and below
the modulus. `R4TransportWideReference` connects that integer reference to
`SourceSamplerByteRank.gammaBytes` through its existing `rank_lt` and
`gammaBytes_value` theorems. The retained `run8_bytes` and
`remaining8_value` already describe ordinary digits and the high quotient.
These are reference/model identities, **not** a proof that Rust's mutable
helper loops return those digit arrays.

The exact optimized `low_base_p_digits` and `add_small_base_p` bodies were
cut without modification into an isolated native crate. Pinned Charon and
Aeneas each exited0. Translation nevertheless emits six external function
axioms, including `from_fn`, mutable `into_iter`, iterator `all`, and
reverse `next_back`. The diagnostic template is committed as `.lean.txt`
and is never imported into an accepted owner. This is a concrete extraction
boundary, not a silently accepted standard-library assumption.

### Query-word and library checks

The kit cuts complete shipped `block_rank`, `query_words`, `QueryScan`
structure/scan/finish, and `queries_from_pairs` bodies. Its source checker
also checks that the contract-scanner body differs only at the named
membership expression. No field, circle, digest or transcript stub is used.

Kani passes:

- arbitrary32-byte little-endian words, low18 mask = modulo262144, and all
  eight by-value array visits in order;
- successful finish exactly at length22, otherwise the exact exhaustion
  error and accepted count, for all lengths0..22;
- indexed membership and the exact Boolean membership contract at **each**
  length0..22, with arbitrary stored words and candidate. Both original and
  strengthened23-harness partitions pass; the latter additionally checks
  the predicate substituted into the contracted scanner.

These are25 distinct accepted component roots, not a complete query proof.
The direct arbitrary-state block comparison times out after300s. Isolated
symbolic-length membership times out after120s; partitioning by length
replaces that attempt and succeeds in23.911s, then25.272s for the strengthened
version. The first contracted scanner attempt finds an insufficient unwind
bound in bytewise `memcmp`, not a source scan counterexample. Replacing
array comparison by22 scalar comparisons and raising the harness loop
bound from10 to24 preserves every unwinding check; that changed attempt
times out after180s. None of these failed attempts is passing evidence.
No cap was raised and no unchanged failed job was repeated.

The existing row31 packet proves list scan steps, stable first22 order,
range, distinctness, rejection and first-stop facts. Our library component
checks narrow its source gap but do not instantiate the complete generated
scan loop or the eight-block caller with those contracts.

### Circle and rho composition

`R4TransportCircleCoordinates.parameter_eq` transports the actual extracted
QM31 parameter to `R0P.SemSource.qm31Sample` at the decoded byte block.
`circle_total_coordinates` then proves, for **every**32-byte block and both
First/Second rows, existence of a successful actual wrapper result whose two
embedded coordinates are exactly `(model block row).1`. The secure branch
uses the retained R72 source execution; singular and CM31-rejected inputs
use the checked row-specific fallback outputs and coordinates. No success,
regularity or canonicality premise remains on this top theorem. This is
stronger than merely showing its result lies on the circle. It is stated
against the retained extracted wrapper, not a new current-caller re-pin.

`R4TransportRhoSource.qm31_total_model` proves that the primitive sampler
always succeeds with precisely the model QM31 value. `rho_success` obtains
the block and primitive success from the actual retained `scalar_k` call.
`rho_call_transport` composes that value with the source duplex block law:
the model row32 result is exactly the embedded returned QM31 and the same
returned source state. It quantifies over arbitrary prefixes and oracles,
but **retains** preceding-state and encoded-frame agreement and a successful
digest interpretation. It does not derive those hypotheses from row31 or
from the frozen verifier. In particular, it does not replace the selected
query advance with the eighth advance.



## Stage 3: prefix composition and remaining boundary

`R4TransportPrefixFrame.opening_frame_eq_iff` proves that, with the same
label, length and payload, equality of the opening preimages is **equivalent**
to equality of the preceding32-byte states. It takes32 bytes on both sides
and uses injectivity of `List.ofFn`; it never computes a concrete transcript.
`absorption_preimage` identifies the model address and source digest parts
for arbitrary row and payload once their state, label and encoded bytes
agree. It also applies before row31, without asserting its returned state.

The surviving ordinary-row interface is verbatim:

```lean
(hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
  (LiteralTranscript.erasePrefix P) = decodeState sourceState)
(hlabel : SelectedTranscriptParams.params.lbl i = decodeByte tag)
(hbytes : SelectedTranscriptParams.params.enc b =
  PublicInitFrame.lengthBytes n.val ++ rawBytes payload)
```

The first25-row source-prefix theorem already exists. It must be connected
to the reached row25/26 records, their exact framed bytes, the row26 P3
reseed (including the S2 tag), and subsequent reached opening payloads.
Local suffix laws retain precisely these byte/state hypotheses. An equality
of sampled values at one block does not prove them.

A second checked obstruction is at the actual pinned `PreparedModel`
interface. `R4TransportBoundaryFreedom.arbitrary_gamma_success` shows that
for any successful row27 source block, overriding `B.gamma` can make the
scalar call successfully return **any** machine value without changing its
returned transcript state. `universal_gamma_property` proves that a claimed
property of every such boundary call must hold for every machine value.
Thus the missing optimized scalar refinement cannot be inferred from block
success or the current free boundary record. This is an interface
countermodel, not a counterexample to the shipped gamma implementation.

| Row | Narrow remaining source/prefix obligation |
|---|---|
| 25 | Current reached circle wrapper/source binding; preceding full25 state; actual validated record bytes equal the selected row25 payload |
| 26 | Same for row26; opening constructor consumes its returned semantic state and performs the P3/S2 reseed |
| 27 | `low_base_p_digits` and `add_small_base_p` machine-array refinement to the proved byte/gamma reference; bind `B.gamma`; reached `y1` frame and prior state |
| 28 | Bind `B.ordinary` to the same low8-digit model and inactive canonical serialization; prior state |
| 29 | Ordinary sampler as row28; exact reached round0 polynomial bytes and prior state |
| 30 | Ordinary sampler as row28; S2 branch and exact folded-root32 || round1 bytes, including length prefix; prior state |
| 31 | Whole shipped scan/first-stop/finish composition with the Lean recurrence, error mapping, eight digest pairs and **selected** advance; reached final-message bytes and prior state |
| 32 | Exact reached empty-payload call; query-selected prior state. The local extracted QM31 arithmetic and block/state composition do not supply row31's state |

Consequently the full frozen33-row prefix transport is **not proved**.
The point/carrier, helper-loop, current-caller, and prefix obligations above
remain separate. No generic endpoint is specialized to an arbitrary boundary
chosen to make these facts true. No new premise replaces R4 and no signature
is weakened: both Headline and R19 are byte-identical to the task base, as
checked in `headline-unchanged.json`.


## Validation

Stage1 was source inspection only. The final focused results are:

| Target module (all exit0) | Attempt | Wall seconds | Peak RSS bytes | Swap |
|---|---:|---:|---:|---:|
| R4TransportGammaFold | 3 | 5.109 | 2865512448 | 0 |
| R4TransportGammaRank | 2 | 3.265 | 2836283392 | 0 |
| R4TransportWideReference | 1 | 3.604 | 3242409984 | 0 |
| R4TransportBoundaryFreedom | 3 | 2.305 | 2246262784 | 0 |
| R4TransportPrefixFrame | 2 | 4.649 | 3468132352 | 0 |
| R4TransportCircleCoordinates | 7 | 27.290 | 3255353344 | 0 |
| R4TransportRhoSource | 9 | 14.989 | 3392520192 | 0 |

All19 new theorem audits, including the private bind helpers, use only a
subset of `[propext, Classical.choice, Quot.sound]`. The exact theorem names,
full axiom lines, commands, source revisions and SHA256s, ordered object paths,
dependency/environment fingerprints, exit status, wall time, peak RSS and
swaps are in `manifest.json`, each attempt directory, and `audit.json` under
`evidence/r4-transport-20261021/`. Failed elaborations retain their diagnostics
and generated `sorryAx` reports; they are not current results. Queued jobs
cancelled before compiler invocation have separate preflight receipts with
null resource/axiom fields, not fabricated compiler measurements.

The early environment failures exposed several distinct retained-cache
issues: incomplete package paths shadowing later packages, missing split
`.olean.server`/`.olean.private` and IR artifacts, and an old function owner
omitting `trace.value` expected by Prepared. A private package union with
pinned nominal owner objects and matched sidecars repairs the environment;
missing selected sampler objects are retrieved read-only from the retained
host closure, with source-indexed plans, hashes and sizes. The circle source
execution object matches the already committed upstream packet pin. No
shared cache or source is overwritten and no dependency rebuild is used.
The failed unchanged `ExtractedPreparedReachability` source probe is retained
and was not retried; the new rho owner inverts only the needed scalar call.
This is **focused cached-object evidence, not a coherent frozen release
manifest replay or C2/P6/R21 discharge**.

Host outcomes and resource reservations are in `host-manifest.json` and
`host-receipts/`; extraction inputs and tool hashes are in `wide-extraction/`
and `toolchain.json`. Every host scope uses MemoryHigh6G, MemoryMax8G,
MemorySwapMax0 and TasksMax64. Failed time-limited jobs retain both GNU-time
RSS and cgroup charged-memory peaks: on timeout the former can omit killed
unreaped descendants, so it must not be read as aggregate RSS. No timed-out
job is accepted evidence. Historical full-crate harness hashes were not
captured before adding unused harness roots; unchanged tested root bodies,
the final source cut and shipped-source hashes are retained. No full-release
reproducibility claim rests on those historical hashes.

The packet's source/receipt/axiom/source-cut audit runs without Lean or Kani:

```sh
python3 -B docs/research/100bit-spend-path-20261013/evidence/r4-transport-20261021/audit.py
```

No existing Lean module, concurrent S1/S3/S4/S5/S9/S10 candidate, M10
instrumentation file, shipped crate or program source was changed. No ELF
rebuild was needed, no keys/accounts were touched, and no push was made.
No full frozen manifest, adversarial/runtime suite, or unrelated reproducible
build was repeated for this open source boundary.

## Continuation: R4_transport2 (2026-10-21)

Branch `codex/cx-r4-transport2-20261021`, base `54054b905`. **R4_transport
remains open.** No boundary premise is removed or replaced. Both Headline
and R19 are byte-identical to that base (`r4-transport2-20261021/audit.json`).
This continuation adds ten modules with23 standard-axiom theorem audits and
36 accepted Kani roots; all current successful receipts record zero swap.
Evidence is under `evidence/r4-transport2-20261021/`.

### Wide machine and reference

The exact optimized scalar division step passes for every u32 limb and
remainder<P. The exact scalar carry step passes for canonical digit<P and
addend<=257. The **complete** shipped carry helper passes against an indexed
reference, including all output digits and final carry. Eight arbitrary-write
reverse-iterator position/frame checks pass separately from the nonlinear
division proof, and the reverse traversal and from_fn callback order pass.
The source splice checker checks the divider occurs identically in both the
optimized helper and the existing extracted indexed division reference. It
also checks the exact indexed carry candidate associated with its retained
extraction; the candidate and its owner files are only read.

`R4Transport2WideReference` proves total execution of eight applications of
that actual extracted division pass, retaining the entire quotient array,
and proves its low digits and remaining value equal the byte-rank model.
`R4Transport2WideBounds` proves the canonical-digit and quotient+1<=257
bounds used by the step checks. `R4Transport2AddReference` proves the actual
extracted indexed carry reference's positional mod/div result. Its cached
objects are fetched read-only with exact existing source/object pins into a
private directory. No shared owner is overwritten.

The remaining wide join is the optimized outer iterator/from_fn shell and
its final quotient-array/debug-assertion embedding into these checked
references, followed by binding `B.gamma`/`B.ordinary`. This packet does not
silently import the earlier extraction's external library axioms.

### Scan, selected state, and prefix chain

The timed-out whole scanner is replaced by23 successful single-source-word
partitions for lengths0..22: arbitrary candidate/stored words/draws<=64,
full stop flag, length/draw update, membership and all array cells. Lean's
`R4Transport2ScanComposition.scan_loop_refines` lifts the exact single-step
relation to the whole loop, and its invariant preserves count/draw caps and
distinctness. `eight_pairs_selected` proves the materialized driver equals
Q22.scanOut with its reached8-word budget, including next-block detection of
success on an eighth word; it assumes no distinctness of advance states.

`R4Transport2CirclePrefix` threads one first-25 checkpoint-state equality
through the two actual retained circle block calls and the S2/P3 reseed.
`OpeningChain.trace_transport` threads ordinary opening calls while deriving
labels and using source length/payload bytes, eliminating repeated per-row
state/byte equalities. `QueryPrefix.source_query_chain` identifies sixteen
actual source digest successes with the eager model chain and selected scan
state. `QueryAbsorb.source_query_prefix` derives the row31 absorb address
from the actual source absorb. `QueryRho.rho_after_selected_query` feeds that
selected result to the actual row32 scalar_k call with its empty frame.
Its remaining `hscan` is explicitly the source/reference-driver result join.

The exact current row30 append expression also passes Kani: arbitrary
root32, round1[224] and arbitrary byte index; output length256 and every byte
is root||round1. `prefix-source.json` checks the reached row25–32 expressions,
all eight eager source pairs, and assignment of the **selected** returned
state. These checks do not construct the frozen parser's literal words.

### Exact remaining obligations

| Row | Remaining source obligation after this continuation |
|---|---|
| 25–26 | Instantiate the successful retained circle calls with the reached frozen validated records and their selected literal messages; connect the first25 checkpoint to that reached caller. The state/reseed composition itself is now proved. |
| 27 | Bind optimized wide helper shells to the checked extracted references and then `B.gamma`; instantiate the reached y1 call/message. |
| 28 | Same ordinary-helper binding; bind actual canonical inactive serialization to `B.toBytes` and the parsed literal payload. |
| 29 | Same ordinary-helper binding; connect reached round0 bytes and model message. |
| 30 | Same ordinary-helper binding; connect the proved root||round1 byte append and S2 branch to the parsed `.second` literal word and caller. |
| 31 | Instantiate the whole scanner's single-step embedding (including its generated iterator owner), finish/error/result-array mapping and materialized caller with the proved reference driver; discharge `hscan` and bind the actual query boundary. Digest-chain/selected-state composition is now proved. |
| 32 | Instantiate the successful empty-payload rho call from that actual returned query state; the query-to-rho model/source composition is now proved conditional on `hscan`. |

These remaining caller bindings cannot be inferred from the current free
Prepared interface. `R4Transport2CallerObstruction.arbitrary_query_state`
and `universal_query_state_property` prove that the query boundary can return
any state for the same query vector and incoming transcript.
`arbitrary_inactive_bytes` proves that its serialization boundary can return
any32 bytes for a fixed inactive element. These are compiled interface
countermodels, not counterexamples to shipped Rust. Consequently a universal
Prepared-boundary success theorem cannot supply these missing source joins.
Neither a boundary chosen to make R4 true nor a new source-law axiom is used.

### Attempts and validation

The new whole division-pass comparison times out after120s. A batch of eight
arithmetic+array position checks also reaches its120s total deadline after
two roots finish; that batch is not accepted as passing evidence. Neither is
rerun. The replacement separates the already-verified scalar arithmetic from
eight arbitrary-write address/frame contracts; all eight pass in4.238s.
Earlier scanner timeouts are never rerun. No memory cap increases.
The CLI preflight failure before adding Kani's required unstable-options
flag is retained separately. All failures retain exact commands and logs.

`manifest.json` records each Lean attempt's target, source/revision hashes,
dependencies, exit, wall, RSS, swaps and full axioms lines; `host-manifest.json`
and its per-attempt inputs/receipts do the same for Kani (axioms N/A). Host
limits are always MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64 with
reservation checks. Timeout GNU-time RSS may omit killed descendants; use
the separately recorded cgroup memory peak for charged aggregate memory.
Every historical generated host-source SHA has an exact text snapshot.

The final offline audit is:

```sh
python3 -B docs/research/100bit-spend-path-20261013/evidence/r4-transport2-20261021/audit.py
```

This is focused cached-object and source-step evidence, **not** a coherent
frozen release replay or R4 discharge. No existing Lean module, protected
candidate/M10 instrumentation file, shipped crate/program, wallet/key or ELF
is changed; no push is made. The R4 design note is the only existing tracked
file edited by this continuation.
