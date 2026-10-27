# V374 plan — D272 recommended artifact B

Recommended recipe pending owner approval; toolchain rustc 1.94.1 unpinned.
No timing samples collected. Target not yet established.

This plan supersedes the historical draft below for new measurements. The successful build is
`B-recommended/receipt.json`, executable SHA256
`898005412d46103cfeffe5740f7892ee01d1e3d73a7293338c62e679445b5e67`.
Source is candidate `237e135561` plus lockfile-only commit `1f02f0ecd7`.
Features are exactly `r1p-check,aspis-r1-cost-probe/ct-host-prover`, with
`RUSTFLAGS=-C link-arg=-Wl,--threads=4`, release/offline/locked/-j4. The build
must show the resolved feature closure; `optimized-terminal` is not requested.
B uses `generate()` (96 bytes), not A's `generate_for_mask_nonce` (64 bytes).
Changing any identity input requires re-audit and rebinding this plan.

The lead schedules **one 90-minute quiet window per kernel family** and a
**separate four-hour quiet window for complete attempts**. No window is
requested or started by this task. The kernel window reserves 10 minutes for
admission/calibration, 65 for samples, 15 for flush/analysis. Complete-attempt
windows reserve 15 minutes admission, 15 pilot, 195 sampling, 15 drain. Stop at
the deadline; report incomplete counts. Pilot runtime must inform the lead's
schedule before the main attempt run. Never silently shrink the target counts
or run outside the window. One capped scope at a time, 6G/8G/swap0/Tasks64,
existing reservation/quiet-host barrier, fixed allowed CPU affinity. Parallel
worker experiments must fix worker count and pin the whole worker set to the
same declared CPU set; a single-thread harness does not measure B's pool.
Abort on competing workloads, cap pressure, migration or window expiry and
retain the receipt. Do not change DOITM, MSRs, firmware or host policy.

Pin CPU model/microcode, kernel/governor/frequency/turbo/SMT/affinity/temperature,
ASLR, counter serialization/overhead, compiler/LLVM/features/link flags and
binary hashes. DOITM OFF and V371 remain substantive. A separately built
in-process dudect harness is a new measurement artifact: pin its source,
executable and normalized kernel instructions/relocations against B. Reject
an equivalence claim if they differ. B's JSON interface cannot inject arbitrary
private witness/entropy classes; its deterministic note fixtures do not supply
a same-public honest witness pair. Whole-process fixture results must retain
that label. No devnet transaction, wallet file or funded key is needed.

| Experiment | Two classes and fixed inputs | Target counts per class |
|---|---|---|
| CT pole scan N1 | Diagnostic canonical, pole-free arrays: mismatch in first limb versus same first limb/mismatch in second; fixed chi, 1024 rows and public masks. Separate full equality diagnostic. Raw slot arrays are not claimed attainable honest witnesses. | 10k warm-up total, 100k initial, 1m maximum |
| Arithmetic/inverse/hash | Fixed valid nonzero versus random canonical operands; zero/nonzero in a separate API-valid diagnostic. SHA equal lengths/segments; Poseidon same arity/rounds. Dispatch policies separate. | 10k warm-up total, 100k initial, 1m maximum |
| 96-byte entropy/expansion/masks | Fixed versus random private seeds, same context/nonce/layout; synthetic zeros/rejections separately labelled. OS acquisition is a separate observer event; never classify it as the 64-byte route. | 10k warm-up total, 100k initial, 1m maximum |
| N2–N6 semantic/validation | Two valid witnesses for the same public statement, geometry, terminal variant and public challenge schedule. Establish native validity before admission; otherwise blocked. Invalid raw inputs only diagnostic. | 10k warm-up total, 100k initial, 1m maximum for isolated guards; full semantic bodies use attempt budget below |
| N7 decimal parser | Synthetic in-memory 64-byte JSON arrays, private seed positions 0..31. First diagnostic compares 1- versus 3-digit bytes (encoded length is the tested observable); second holds total digit count fixed: 16 one-digit + 16 three-digit bytes versus 32 two-digit bytes, identical public tail. Zero-first-digit stratum separate. Arrays are parser-valid, not claimed valid Keypairs. Valid key-file end-to-end tests require separately retained validity/class construction; no real keys. | 10k warm-up total, 100k initial, 1m maximum |
| Complete attempt | Same-public valid witness populations; include 96-byte entropy, reservation, all retries/rejections/poles/errors, semantic/commit/open/P_R1 work and cleanup. Unconditional timing primary; success/status strata descriptive only. Fixture-only timings separate if same-public pairs unavailable. | Pilot 10/class; main 100/class, maximum 1000/class; 20 warm-up total; low-powered descriptive results if window limits counts |

A family is not one pooled statistic: preregister each kernel, input class,
variant, dispatch path and worker policy separately. Freeze a public random
experiment seed and balanced randomized class order. Generate inputs and
allocate outside isolated kernel intervals; full-attempt intervals deliberately
include allocation, entropy and cleanup. Prevent dead-code elimination.
Retain only synthetic input construction/public input hashes, timings, classes,
status/attempt/rejection/refill/exhaustion/failure counts, counter CPU IDs and
class-blind exclusions; never export live entropy, recovery notes or keys.
No selective resampling of failures or class-dependent filtering.

Use serialized invariant-cycle measurements and wall time for threaded/full
attempts. Predeclare Welch first-order t and centered-square second-order t,
means/variances/confidence intervals and counts. Kernel checkpoints are every
100k samples/class; complete attempts every 100/class. |t| > 4.5 is a diagnostic
trigger, with every checkpoint retained and multiple tests/optional stopping
explicitly reported. Preserve outliers; clock/migration failures alone may be
excluded by one class-blind rule with counts per class. A threshold crossing
requires investigation. No crossing means only no detected difference for
these classes, setup and budget; it never establishes absence of leakage.
V374 remains OPEN/P until qualified samples and lead review; the plan itself
removes no premise. N2–N6 invariant proofs, V352–V364 joint law, V370, V371,
V373 and V396 remain independent obligations. T remains capped at its three
existing fields.

---

# Historical V374 draft for the unbuilt original B

Proposed only: no timing samples collected. The lead schedules a quiet window.
The target is B from `237e13556180d2ce0320a2760f89b35b5f4f02bb`, built by the
exact devnet R1 recipe, toolchain unpinned (host default rustc 1.94.1).
B did not build: `B/receipt.json` records exit 101 and has no binary SHA256.
No executable is currently eligible for this plan. After a lead-approved
corrected candidate is built, bind this plan to its receipt SHA256, never the
older retry example. Rebind all
addresses and repeat this plan's identity review if source, features, compiler,
link flags or executable changes. In particular, adding `ct-host-prover` is a
different artifact. B's actual entry uses the 96-byte generator, not A's
proof-account/64-byte generator. A later adopted proof-account B must be rebuilt
and audited before it replaces this target.

The unmodified JSON `devnet_spend` interface synthesizes deterministic fixture
notes and reads fresh OS entropy internally. It cannot accept arbitrary two-class
witness/entropy pairs. Consequently an in-process dudect harness is a **new
measurement artifact**, whose source, compiler, executable SHA and byte identity
of each tested kernel must be pinned separately. Do not call its timings whole-B
measurements, and do not modify B or export secret recovery/key files into
receipts. A new wrapper/link does not inherit B addresses; compare normalized
instructions/relocations and reject a kernel-equivalence claim if they differ.
Full-process B timings may be retained as supplementary fixture-only data.

Before admission, record CPU model/microcode, kernel, governor, frequency/turbo
policy, SMT topology, affinity, temperature, rustc/cargo/LLVM, feature closure,
RUSTFLAGS, ASLR, and hashes. DOITM remains OFF under Secure Boot lockdown (V371
substantive). Do not change MSRs, firmware or host policies. Verify the lead's
quiet window covers the entire run and the quiet-host/Docker-cap barrier admits
it. One scope only: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64;
use the host reservation barrier and an allowed fixed CPU affinity. Abort on
co-running workloads, migrations, cap pressure or window expiry. Preserve the
failed admission/run receipt, no opportunistic off-window retries.

Preregister these separate experiments:

1. Arithmetic/hash kernels: fixed valid nonzero operands versus randomized
   valid operands; separately zero versus nonzero where the public API permits
   zero. SHA-256 uses equal lengths and equal segment boundaries, fixed versus
   random private bytes; exercise both software and hardware dispatch only if
   the actual target can select them. Poseidon uses fixed versus random
   canonical 16-limb states, fixed round schedule. Do not mix lengths or dispatch
   policies between classes. Label zero-boundary timing separately from the
   accepted witness domain. These isolate branch/address findings and V371;
   they are not whole-prover witness tests.
2. Masks/entropy: fixed valid public geometry, fixed nonce/context and class
   assignment independent of the secret draw. Test fixed versus random private
   seeds in the harness with exactly the same sampler API. Retain attempt,
   rejection, refill, exhaustion and OS-failure labels as separate observer
   events. Never drop or resample a class selectively. Synthetic P rejections
   and zero blocks are diagnostic strata, not samples of the honest law.
   D268 rejection-count findings remain V352–V354 joint-simulation obligations.
3. Helper/semantic/opening kernels: two valid witness populations satisfying the
   same public statement, layout, shape and terminal variant. A fixture note
   number, transfer versus withdrawal, amount, commitment or different lane is
   not a same-public witness pair. Establish same-public validity through the
   retained compiler/relation checks before a qualifying run. Precompute test
   inputs outside the timed interval, and retain only public input hashes,
   class construction and success/error counters. If a valid same-public pair
   cannot be constructed, record that blocker; do not substitute two public
   transactions and claim witness privacy evidence.
4. Complete attempts: include commitments, semantic work, openings, P_R1
   elimination/checking, rejection/pole/error prefixes and cleanup. Predefine
   both an unconditional observer timing and per-status descriptive strata.
   PoleBad is charged under D268; report its frequency and timing, without
   treating conditioning on success as a replacement for the full experiment.
   No proof publication, devnet transaction or new funded account is needed.

For each feasible experiment: random balanced class assignment from a retained
public experiment seed; warm-up 10,000 untimed calls; initial 100,000 samples per
class, maximum 1,000,000 per class, checked at fixed 100k checkpoints. Alternate
class selection randomly, keep public lengths/geometry identical, prevent dead
code elimination and move allocation/input generation outside the kernel interval.
Measure with a serialized invariant-cycle counter; record overhead calibration,
CPU ID and migration counts. Retain raw timing/class/status samples and all
predeclared exclusions. Exclude only failed clock/migration measurements under
one class-blind rule, and report exclusion counts by class; preserve other
outliers and provide robust descriptive summaries alongside Welch's t.

Report first-order Welch t (including |t|>4.5 as a diagnostic threshold), means,
variances, counts and confidence intervals, and second-order centered-square t
as a separately declared diagnostic. Retain every checkpoint and account for
multiple tests/optional stopping: a threshold crossing prompts investigation,
not an unqualified p-value. A run with no crossing means only no detected
difference under that setup and sample budget. Measurements never establish
absence of leakage, discharge V352–V364, or remove V371. V374 stays OPEN until
qualified samples, setup and analysis are retained and reviewed by the lead.
