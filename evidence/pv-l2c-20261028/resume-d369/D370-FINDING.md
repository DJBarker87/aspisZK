# D370: N3 guard constancy is false on successful canonical preparation

Target not yet established. Stop: checked native counterexample against the
frozen candidate source, as explicitly required by the D369 prompt. No further
proof, Kani, replay or measurement job is launched after this finding.

Worktree: `/Users/dominic/ZK/.worktrees/pv-l2c`; branch:
`codex/pv-l2c-20261028`. Recovery entry: 3ba01cb05b. Executed probe source
revision: 47e67bf36d (see canonical-n3-probe5-invocation.json). No source under
crates/ or programs/ changed. No push, deployment or wallet/key operation.

## Checked input and observed outcomes

`canonical-n3-probe5/main.rs.txt` is the receipt-hash-matching executed probe.
`out.log` retains the full public statement, witness, snapshot and 800 snapshot
bytes; the constants and construction in main.rs.txt reproduce both cases.
The only witness difference is recipient.owner_key[0] = M31(0) versus
M31(2147483647), with P = 2147483647. Input value is 1000; recipient/change
values are 600/400. Both snapshots decode successfully and both full forest
transfer compilers return Ok. Assertions check equality of the entire original
public statement AND the returned public transition, including afterstate.

| Observation | Raw 0 | Raw P |
|---|---|---|
| Canonical snapshot decode and full compiler | Ok | Ok |
| Raw noncanonical compiler cells | none | c1[0][444] = P |
| Native mask construction/application | Ok / Ok | Ok / Ok |
| Native inactive balances | 16 C1 / 10 mask-only columns | 16 C1 / 10 mask-only columns |
| Row 444 | inactive; outside relation-free mask cells | same |
| Cell after masking | remains 0 | remains P |
| Exact-body check_base_column diagnostic | Ok | Err(Public) |

The bad case additionally calls the unmodified native public entry
`prove_masked_fixture` (S2, seed [29;32]): Err(Semantic). It also calls
`StateOnlyAttemptSecrets::generate_for_mask_nonce([31;32])` with actual OS
entropy and `prove_masked_attempt` with a durable nonce store:
Err(Semantic), with no reservation I/O error. The nonce ledger is retained on
the host. No random secret seed is printed or committed.

The concrete same-input mask diagnostic uses private entropy [19;32], nonce
[17;32], binding [23;32], and context public digest [13;32]. It is a successful
particular random tape, not a distribution theorem. Raw P survives because
this cell is not a mask cell or a balancing dependent. Inactivity does not
imply that every cell in that row is overwritten. The earlier probe's false
assumption that row 444 was active is retained as a failed diagnostic.

## Domain and native evidence boundary

The requested domain is successful `PV_RunJoin_CodecOuter30.run`: snapshot
decoding followed by the full compiler, retaining both Result layers. It does
not require canonicality of every raw private witness limb. The new accepted
`PV_L2C_CanonicalCaller.transfer_entry` (50302) transports any such success to
exactly ConsumerBoundary25.HonestInput using CanonicalHonest31.transfer.
Neither that carrier nor its success condition was strengthened here. The
native example satisfies the corresponding operational success conditions;
we do not claim a separately kernel-reduced numeral encoding of this example.

The source review identifies the reason: the forest compiler validates public
and common input, output values and computed commitments, but does not reject
this raw recipient owner-key representation. Field decoding identifies P with
zero; equality after decoding cannot establish the raw bound required by N3.
CanonicalCoverage31 and SnapshotAgreement31 do not add that missing raw bound.

`guard-probe-body-check.json` checks that the diagnostic check_base_column and
inactive_sum_m31 bodies match the frozen native bodies modulo whitespace;
there are no changed calls, constants or error branches in those bodies.
The actual semantic caller clones these native columns, then scans lane zero
first in check_semantic_columns before the first commitment, challenges or
helper. P at row 444 therefore selects the rejecting raw-range branch. The
public prover API result is independent additional native confirmation.
The private semantic module was not instrumented. This is a source-checked
finite counterexample, not a new universal structural (K-1 substitute) link,
a complete native trace-refinement theorem, or a timing measurement.

This is the instructed L2 counterexample on the specified successful-
preparation carrier. The rejection precedes helper challenges and cannot be
hidden inside the already charged poleBad event. No new bad event is introduced.
Excluding the input by adding guard success or raw-column canonicality as an
extra HonestInput assumption would change the requested domain and is not done.

## Validation and retained failures

The private native view verifies all 437 selected source/manifests/assets;
seven overlays use plain rsync and the unchanged base is linked read-only.
`private-native-view.json` and probe5-source-check.json retain hashes. The
probe uses optimized cargo run --release --offline -j 4, 6G/8G/swap-zero scope,
TasksMax=64; time is optimized compilation and the named finite diagnostic.
Probe5 exit 0, wall 0.904944443 s, sampled aggregate peak RSS 184541184 bytes,
swap 0. Source hashes, cgroup controls, command and source revision are in the
raw receipt/invocation. #print axioms is N/A for this native diagnostic.

Probe2: exit 101, own grouped import syntax error. Probe3: exit 101, own
private-module access error. Probe4: exit 101, wrong active-row assertion,
before masking. All source snapshots, outputs, metrics and replacement notes
are retained. Probe3's first admission was refused; its same named probe was
retried after more than 180 seconds, with no compiler or ID charge on refusal.
No failed input was rerun unchanged; no cap was raised. The compiler-only
probe1 from the previous session was reused as historical evidence, not rerun.

D369 Lean charges remain 3/100: 50300/50301 failed, 50302 passed; 97 remain.
D370 adds zero Lean and zero Kani. Overall historical Lean total is 143;
six historical Kani invocations remain unchanged. No out-of-block ID used.
The explicit counterexample stop, not exhaustion, leaves 50303–50399 unused.
Final audit IDs 50397–50399 are not launched after the stop. The already
accepted four CanonicalCaller theorems print only propext, Classical.choice,
Quot.sound in out-50302.log. No new final combined audit is claimed.

Both original transfer and withdrawal non-vacuity proofs, including the
concrete field instance, retain their unchanged passing audit 44898 and
standard axioms. The prior combined audit 44897, focused replay 44899 and
1456-object closure check are reused at their documented scope; they do not
prove this false N3 invariant. Kani-6 codec PASS stays suspended under K-1;
Kani-1/2 are pre-verification failures and Kani-3/4/5 timeouts. No
Option<fn>-dependent PASS is introduced or credited; K-2 quarantine stands.

## V352/V354/V357/V360 before and after

| Row | Before D369 | After D370 | Retained residual |
|---|---|---|---|
| V352 | OPEN/P, bucket b | OPEN/P, bucket b | E1/E2 native entropy streams, retries/failed prefixes, witness-independent failure/public signal and deployed RunJoin/simE observation coupling |
| V354 | OPEN/P, bucket b | OPEN/P, bucket b | Same-attempt sampler/source/caller geometry and complete stream/observation transport; N2 whole-caller constancy remains unproved |
| V357 | OPEN/P, bucket b | OPEN/P, bucket b; N3 counterexample recorded | Raw N3 range constancy is false on the current success domain; native helper/inverse and oracle/interpolation/running-claim association also remain |
| V360 | OPEN/P, bucket b | OPEN/P, bucket b | Public packed-mask/column origin, full balancing caller and observation/certificate transport; no universal N4 or N6 native constancy claim |

Removed: zero endpoint/deployment premises and zero rows. Added, weakened or
changed: zero premises, quantifiers, observers or simulators. T is still exactly
entropy_law, entropy_kernel, observation. The N3 residual is now a checked
failure of the proposed invariant, rather than merely an unproved implication.
No native constancy theorem is claimed for N2/N4/N5/N6. Their previously
accepted local complete-Result, parser, decoded helper/sumcheck and scoped
balancing facts remain at their original scope. The new CanonicalCaller
transport supplies successful-preparation entry, not missing raw range.

Next concrete deliverable for the lead: decide the frozen implementation/domain
repair for raw witness representations, retaining this input as a regression
case, then prove its source/domain correspondence before restarting N2–N6.
No repair, domain restriction or new trust item is silently applied here.

`HOST-CLOSE-D370.json` verifies the collected native receipt/output hashes and
that all 437 native source hashes still match after execution. No L2C scope
remains active. The 179868 KiB rebuildable canonical-probe Cargo cache was
removed; the raw receipts, source view, durable nonce ledger and pinned Lean
cache remain. No wallet or account key was created, modified or cleaned up.
