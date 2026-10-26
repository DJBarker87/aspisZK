# Pool writer round 5 handoff

Target not yet established. `PoolS2_Write.accepted_p1_writes_planned` is NOT
defined or proved. No concrete accepted attacker-chosen checkpoint write was
found. No global soundness ledger row was removed and no trust item was adopted.
Option B remains the adopted release scope.

## Established and reusable

Native host checks:15/25 Kani runs pass. Exact scopes and source snapshots are
in K002,K007,K008,K010,K011,K013–K018,K020,K022–K024. They cover original
first-checkpoint bump output; remaining strict-master identity/policy field
bindings to the SAME arbitrary384 image; native key0/key9 distinction on12
actual accounts; original count and payer/System result/error checks; bounded
instruction codec; shared-read/strict-decode/Box bump; all-result selected-byte
frame and mutable reborrow after guard Drop; same192-image checkpoint signing
seed contents. K022–K023 intentionally exclude enclosing metadata/PDA/identity
checks. K024 checks decoded signing-seed contents, not an invoked System helper.
These are host helper checks, not an enclosing original P1 proof or SBF proof.

Lean local/source helpers: `PoolS2_UniqueExact` proves the complete extracted
P6 full-byte key projection; native/P6 equivalence remains open. Count,
PayerExact, Instruction, PolicyExact give exact local acceptance laws with
canonical owned carriers and documented pure equality/constants. PDA
Master/Lane/Checkpoint modules derive SAME SDK create/find arguments and
returned values from their actual source-adapted helpers. SDK children remain
explicit functions; source/runtime/effects/query interpretation is unproved.

`PoolS2_EntryMaster.accepted` and `StagePrefix.accepted` use ONE accepted partial
owned master stage to derive original entry-buffer decoding, SAME decoded
mint/bump SDK create arguments, self-key, exact instruction and selected
payer/System predicates. Master/checkpoint data-cell inequality follows from
that same full-byte prefix and entry alias coherence, not a separate hypothesis.
This is explicitly a partial OWNED reference: no native AccountInfo snapshot,
Box allocation, borrow/cleanup or caller effects interpretation is claimed.

`PoolS2_PlannerExact.accepted_iff` characterizes the full unrestricted pure
VALUE/ERROR reference on complete canonical Master/eight full Lane/root/bump
inputs. It derives source-ordered validation, fixed lane order/master/capacity,
SAME extracted chronology and exact checkpoint/next-master assembly. The final
next-master validation premise is removed by `NextValid.derived`, rather than
packed into an assumption. PlannerBindings/Indices/Chronology/First derive full
field binding, actual selected lane sequence, increment without overflow,
repeat nondecrease/strict progress and first sequence0/next1. No coherent-fixture
class is substituted for arbitrary inputs. Native original planner equivalence
is still missing; these results cannot instantiate it by themselves.

Before/after: independent successful prefix/master/validation/assembly facts
are conclusions of SAME accepted calls **inside these explicitly named local
or reference functions**. The deployed S2 antecedents are unchanged. Decoder,
PDA, SDK/runtime/oracle/source/ELF and original caller joins are retained as
open proof obligations, not new cryptographic assumptions. No quantifier or
release target was lowered.

## Remaining concrete gates

1. Original F744–789 full unrestricted pure-planner decomposition on ONE actual
   original execution, with decoded original master/eight lanes/root/PDA/fresh/
   encoder outputs. K021/K025 still time out. The reference theorem does not
   close this gate.
2. Original AccountInfo reads/strict decoder/PDA/self-identity/Box joins and lane
   stored-bump fast/fallback path, all from original immutable buffers and
   with source error ordering and actual guard cleanup. Original master/Box
   AENEAS007 fails SymbolicToPureValues.ml:878. AENEAS011 strict codec fails
   InterpReduceCollapse.ml:1991. Full planner AENEAS004/008 also fails there;
   isolated digest AENEAS009 fails TypesAnalysis.ml:372. Isolated actual
   policy/master validators AENEAS010 succeed. No tools were repaired.
3. Original F2130–2188 caller prefix, SAME returned plan, second fresh
   preparation, decoded-image seeds, System CPI state effects, post-CPI guard,
   dual mutable borrows/copies/compiler cleanup, and SAME canonical committed
   action/source invocation/key. Compose from post-System store with existing
   PoolU/PoolW only after these source gates. No unit-return CPI law is adopted.
4. Separate option-B exhaustive alternate-role/dispatch/close/CPI
   noninterference, real genesis/assignment/rollback/commit/load association,
   and same-world proof/public binding. Upstream master/lane correctness is
   separate from immutable-record provenance and spend soundness.

The next native deliverable remains the original accepted P1 same-plan/caller
certificate, not another reference/history wrapper.

## Ledger priority: ASC8 versus verifier CP

`PoolS2_LEDGER.md` inspects literal types. L091–L096 refer to verifier-owned
CP1768; L097/L098 bind complete proof/ASF8 public inputs through the same-world
digest/collision route. None is an ASC8-origin-only binder. P1/ASC8 origin alone
does not discharge them. In particular CP protection does not require AS8C to
succeed: foreign-owner write prohibition plus exhaustive forwarding exclusion
can support the CP noninterference argument, once connected to actual runtime.
L180's literal deployment alias expands CP protection L094–L096. The lead's
adopted option B assigns the **additional ASC8 origin/retention obligation**
under that umbrella; P1 is required for that extension. It has no separate
ASC8-only literal numbered binder in S2X_RuntimeRetention. Do not drop this
owner-assigned obligation or conflate the two checkpoints.
L081 `p1` is ROM P1Realization, not Pool inventory P1. L186–L188 are generic
release lowering/replay/audit obligations, not ASC8-only semantics.

## Runs, freeze and stopping condition

Stopped because the entire assigned budget is exhausted:100/100 actual Lean
invocations and25/25 Kani runs. Kani exhaustion did not stop Lean. Lean66
successful compiles/34 diagnostic failures;66 delivered modules all match
successful source snapshots and standard-only individual axioms. Kani15 pass,
9 timeout,1 compile error. No timed-out/memory-killed job reran unchanged; no
cap was raised. There were no memory-killed runs. Rust used optimized builds;
all host scopes high6G/max8G/swap0/tasks64, Lean-M7000; no own active scope remains.

Final focused aggregate audit L100 **exits1**:133 entries print standard axioms,
but three print commands mistakenly double-prefix PoolS2_Unique. The actual
three roots printed correctly in L001. The failed audit is retained as evidence
and excluded from delivered lean/. No101st attempt was run; do not call this
a green aggregate audit or a coherent release replay.

`PoolS2_RUNS.json` indexes exact targets/commands, status, wall, peak RSS, swaps,
revision/source hashes and full axiom results; individual receipts additionally
pin dependency objects and preserve stdout/time/source versions. Lean measured
sum185.48s, max time peakRSS4384988KiB; Kani measured sum1889.81s, max time
peakRSS5359904KiB. Outer-timeout time RSS can miss descendants; raw cgroup peaks
are separately preserved. All swaps0. These are focused-run metrics, not
package/release costs or a cryptographic security bound.

`PoolS2_validate.py` passes: all157 frozen compiler inputs match locally and
on host; current proof source/objects and tools pinned; receipt snapshots/caps/
axioms/allowed prefix verified. HOST_FINAL/TARGET/INPUTS/VALIDATION contain exact
freeze data. Initial inherited FREEZE still carries PoolT's old budget15;
TARGET records effective user budget25. Proof-only resolved locks are included;
transitive build/proc-macro differences from production are explicitly excluded
from coherent release adoption. Canonical SDK leaves2.3.0 AccountInfo/2.4.0
Pubkey/2.2.1 SDK IDs are recorded where used; pre-pin K005/K006 lock is retained.

No shipped source, cfg(kani) shipped harness, features, production lock, keys,
accounts or funds changed. No SBF/ELF rebuild trigger. Inherited pins remain:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
These are inherited artifact pins, not a new source-to-SBF/live deployment proof.
Coherent S2I and Hist/Hiq/Hir/PoolW/PoolV/PoolU/PoolT objects were reused; no
package/frozen manifest/SBF/adversarial replay was run. Only own PoolS2 prefix
and evidence directory changed. No other worktree/worker candidate touched.

Branch codex/cx-pool-write5-20261026. Local stage commits:4b324656b7,
bbfde8f835,8253066231,3280a10f28,69023fb3a1, plus final receipt/handoff commit.
No push.

Whitespace check: editable proof modules, handoff/docs and validator pass.
The raw-inclusive base diff check exits2 for original tool stdout/generated
unimported templates' whitespace; these diagnostic bytes are deliberately
preserved. PoolS2_WHITESPACE.json records both results. No proof run was added.
