# Part 55: native collection and caller bindings

Target not yet established. Branch `codex/cx-prover-commit55-20261023`.
Only J10700–J10799 are authorized. No shipped source changed.

## Endpoint before

The full verbatim deployed endpoint is retained in
`../../100bit-spend-path-20261013/evidence/prover-commit55-20261023/endpoint/before.lean.txt`.
Its RustProverRefinement premise remains explicit.

## Stages

Stage 1 establishes the extracted native length guard equals the retained
height guard for every input list of length 2^h, h≤8, every trait record,
node array and starting depth. The collector output lengths are derived;
no canonicality or arithmetic-success hypothesis is needed for equivalence.
The added proof fuel is unreachable on all branches covered by this theorem.
This is not yet a native-recursion execution theorem.

J10700 checks the exact new extraction (exit 0, 1.72 s, 2636676 KiB RSS,
zero swap). J10703 proves `R1Z.ProverCommitEncoderGuard55.equivalent`
(exit 0, 2.57 s, 4122004 KiB RSS, zero swap), with printed axioms
[propext, Classical.choice, Quot.sound]. J10701/02 are retained failed drafts:
Boolean simplification and the Vec.deref coercion required explicit handling.
No limit was raised. Exact revision, source hash, dependencies, command and
full diagnostics are in lean/J10700–10703.json.

Charon/Aeneas accept the structurally recursive guarded owner (1.267/0.458 s,
215612/64944 KiB, zero swap). Every reused collector declaration is byte-equal
and recorded in encoder-guard-callee-binding.json. The native length guard is
retained; the fuel assertion is an explicit proof instrumentation boundary.

Complete actual Rust `collect` expressions, including allocation, both
iterator paths and output lengths, are checked at length 256 for arbitrary
raw M31 and QM31 cells. An arbitrary selected output index covers every cell.
No iterator, allocator, Vec or field method is stubbed. M31 passes in 22.095 s
(1349988 KiB); QM31 passes in 128.338 s (4022108 KiB), both exit 0, zero swap.
The exact receipts are m-split-256-v1 and q-split-256-v2. RUSTFLAGS supplies
opt-level=3 despite Kani's Cargo dev-profile banner. The scope is 6G/8G,
zero swap, 64 tasks. These are compiler-pinned native collection checks;
smaller recursive lengths, WideExact and caller composition are still open.

The source revision is the task base in revision.txt (the first native input
receipts abbreviate it as 341584654f). Exact source snapshots and hashes are
retained. No shared object was overwritten; cache links are read-only.


## Stage 2: guarded values, interpolation, prefix and optimized power

J10704 proves complete canonical guarded evaluation by composing the guard
equivalence with the retained generic evaluator. J10705 derives all owned
partial sums and the standard round polynomial from the per-call oracle
results at actual source sample points; no polynomial or sample-sum array
image is a premise. Per-oracle result correctness and the prefix relation
remain explicit. J10710 derives the semantic index relation and source
sample/tail/next-alpha prefix preservation. Initial prefix is unconditional;
the source update reads exactly semantic position 15+r. These local results
do not yet bind the entire native round driver or its semantic oracle.

J10706 checks an exact recursive owner of CM31 power using the native bit
condition, optimized square, and right shift. J10711 proves success,
canonicality and acc*base^exp for every u64 exponent. Unlike the previous
multiply-square owner, this owner calls the actual optimized CM31.square.
Every reused extraction declaration is byte-identical, recorded in
encoder-native-nodes-callee-binding.json. Native while-loop composition
remains a distinct step. J10707/09 are failed shift-transparency/let-rewrite
drafts; J10708 is a failed platform-dependent usize addition draft. The
replacements use a concrete one-bit shift and the proved bounded addition.
All accepted printed axioms are standard only.

| Attempt | Exact module | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| J10704 | R1Z.ProverCommitEncoderGuardValue55 | 0 | 1.72 | 4100224 | 0 |
| J10705 | R1Z.ProverCommitSemanticInterpolation55 | 0 | 2.28 | 4131836 | 0 |
| J10706 | AspisR1ProducerRelease47.EncoderNativeNodes55 | 0 | 1.30 | 2635072 | 0 |
| J10710 | R1Z.ProverCommitChallengePrefix55 | 0 | 1.97 | 4125740 | 0 |
| J10711 | R1Z.ProverCommitEncoderNativePower55 | 0 | 2.51 | 4116108 | 0 |

The optimized power extraction exits 0/0 (1.133/0.313 s,
213520/61776 KiB RSS, zero swap). The reservation preflight waited before
launching when another 8-GiB scope would exceed the 55-GiB reservation.

All native smaller even/odd collections now pass at lengths 2,4,8,16,32,64,
128 for M31, QM31 and WideExact. No allocator, Vec, iterator or callee is
stubbed. The largest smaller check, WideExact-128, exits 0 in 177.963 s at
5575076 KiB RSS with zero swap. Exact commands, scope limits, source revision,
hashes, snapshots, wall/RSS/swap and raw logs are in the named receipts.

The full-record WideExact-256 check was stopped during memory growth at
6456720 KiB (71.837 s), exit 1, zero swap; no cap was raised and it was not
retried unchanged. The replacement verifies output words separately, while
retaining the complete allocation and both native collect paths. Word 0
passes in 88.255 s at 4333640 KiB, exit 0, zero swap. Remaining words are
being checked independently; no complete WideExact-256 claim is made yet.

## Stage 3: semantic guard and final-round composition

J10714 proves the actual intended semantic model function's degree bound,
original-round decomposition, initial/chain/terminal guards, and terminal read
from refPayload+L. J10716 identifies every shifted model round polynomial
with refPayload+L after shift, and proves its boundary and terminal laws.
J10718 composes the source partial sums, interpolation and actual inverse/shift
producers into the entire round-9 polynomial of that model payload. This
retains explicit per-oracle-call correctness, challenge prefix, non-half, and
the two source terminal-input images. It does not promote those input cuts
to a whole native semantic implementation theorem.

J10720 proves the canonical source boundary comparison and composes the
actual source polynomial evaluator with each next boundary guard. The
polynomial images and initial running input image remain caller obligations.
J10722 reassembles all eight independent WideExact component equalities
into complete ordered list equality and connects that list to the extracted
strided collector. Native Kani results remain external evidence, not axioms.

| Attempt | Exact module | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| J10714 | R1Z.ProverCommitSemanticModel55 | 0 | 2.89 | 3613976 | 0 |
| J10716 | R1Z.ProverCommitSemanticRounds55 | 0 | 2.80 | 4168316 | 0 |
| J10718 | R1Z.ProverCommitSemanticFinal55 | 0 | 2.24 | 4183196 | 0 |
| J10720 | R1Z.ProverCommitSemanticGuards55 | 0 | 2.30 | 4149812 | 0 |
| J10722 | R1Z.ProverCommitCollection55 | 0 | 1.77 | 4100584 | 0 |

Every printed accepted axiom is standard only. J10712/13 are type/transparency
drafts; the latter hit the default recursion limit on a payload projection.
J10715 repeats a rewrite already applied to both occurrences. J10717 hits the
unchanged heartbeat limit under a polynomial `change`; J10718 uses a named
identity. J10719 uses a reserved identifier and lacks local equality
decidability. J10721 needs zero-add normalization before list transitivity.
All rejected snapshots/diagnostics are retained. No Lean limit is raised.

All eight WideExact-256 selected-word checks now pass with complete native
allocation/collection, arbitrary raw input words and arbitrary output index.
The word receipts are e-split-256-word0-v3 through word7-v3, all exit 0, zero
swap, with peaks approximately 4.13 GiB. This completes the split collection
checks for every actual recursive length/type used by the caller.

Native constructor-order checks at lengths 4,9,10, semantic challenge arrays,
and canonical M31/QM31 projection round trips also pass. The constructor
v3 diagnostic is an intrinsic memcmp unwinding failure; v4 changes the
comparison to a selected component and covers its remaining tiny comparisons.
An earlier reservation hold launches no compiler. All native scopes stay
6G/8G/zero-swap/64 tasks.

The full native CM31 arithmetic-step comparison times out after 180.568 s
(169536 KiB RSS, zero swap). A different release-flags preflight is rejected
by Kani because it requires overflow checks; no analysis runs under that
configuration and it establishes nothing. The symbolic square/power proofs
remain valid, while the native arithmetic-step gate is not claimed proved.
The channel-0 v3 failure is confined to generating 1024 arbitrary input cells:
its 260 unwind bound covers the collector but not that input constructor.
The revised harness explicitly covers that 1024-step setup; memory caps stay
fixed. No failed native input is replayed unchanged.

## Stage 4: native node output and instantiated retained Poseidon caller

J10729 proves literal canonical point and individual-node result equality
between the optimized square-based owner and the previous geometry owner.
J10732 derives the entire nine-cell source array on valid native indices,
including canonicality and exact node values. Its inputs satisfy j<262144
and d+left≤9. The earlier broader arbitrary-state fill-equivalence drafts
(J10728/31) are not claimed: unknown result continuations caused kernel memory
failures at 7169504/7169024 KiB. The replacement proves the real bounded
successful caller by consuming named per-node results and symbolic array
updates; it finishes in 2.15 s at 4125248 KiB, zero swap. No cap is raised.
J10723 checks the new exact geometry extraction, with all retained declarations
byte-equal. J10728 also exposes an omitted U8 subtraction import/incorrect
counter type; those failed snapshots are retained.

The retained evaluator source cut V12 is checked at J10724 (3.97 s,
4127652 KiB), using its exact unchanged source. No shared object is overwritten.
J10725 is retired without compiler invocation because the first proposed import
was uncached. J10726/27 are qualification/transparency drafts. J10730 initially duplicates the callable result already established in part 53.
That duplication is superseded by J10735: a small equality transfer from the
retained QName evaluator to the existing part-53 callable theorem. J10736
rechecks the dependent composition. The branch-contract discharge was already
achieved in part 53; the new result is its QName interface instantiation.
Public preparation success and the source-cut/frozen-source binding remain
explicit. No new native terminal or whole simulator closure is claimed.

Accepted Lean results:

| Attempt | Exact module | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| J10723 | AspisR1ProducerRelease47.EncoderNativeGeometry55 | 0 | 1.11 | 2637584 | 0 |
| J10724 | PoseidonCandidateProjectedEvaluatorSourceV12 | 0 | 3.97 | 4127652 | 0 |
| J10729 | R1Z.ProverCommitNativeGeometry55 | 0 | 1.83 | 4103904 | 0 |
| J10730 | R1Z.ProverCommitPoseidonCallable55 | 0 | 2.35 | 4151588 | 0 |
| J10732 | R1Z.ProverCommitNativeNodes55 | 0 | 2.15 | 4125248 | 0 |
| J10733 | R1Z.ProverCommitComposition55 | 0 | 1.91 | 4203144 | 0 |

All accepted axioms are standard only. The optimized geometry extraction
exits 0/0 (1.342/0.370 s, 212180/65120 KiB, zero swap). Full exact source,
dependency, revision and output evidence is retained per receipt.

power-control-trace-v4 passes in 1.500 s at 155988 KiB, zero swap. It checks
branching, operation operands/order and returned-state use with open arithmetic
calls; it does not replace the timed-out full arithmetic comparison. The actual
square and power operations are proved separately in Lean.

All four complete native M31 1024→256 channel collections pass (receipts
m-channel-0-v4 through m-channel-3-v4), approximately 99–110 s and 2.76 GiB,
zero swap. The full-record QM31 channel-0 gate is stopped during memory growth
at 6484584 KiB (146.175 s), zero swap, and is not retried unchanged. Its
replacement checks separate output words while preserving the full native
collection. Those checks are ongoing; no complete QM31 channel claim yet.

The frozen/candidate Poseidon function inventory identifies 19 reachable
local functions. Fifteen match after removing comments/whitespace; four
have explicit diffs in source-diffs/. They are the two low folds/constructor,
external local constructor, external linear row loop, and internal constructor
uses. Field.rs and field/wide_exact.rs are byte-identical between frozen and
retained inputs. The Poseidon constants file differs only by an appended
proof-only reference module. Token equality is an inventory, not a semantic
proof of those four changed functions. Native focused bindings are ongoing.

## Stage 5: complete owned semantic oracle and guarded entry points

J10740 transfers the existing part-53 complete terminal model through the
literal QName source interface. J10744 proves both directions of the raw
QM31 carrier conversion, canonicality and decoded point equality. J10746
constructs the actual zero-claim terminal call at sem[0,1,2,13], zc=sem[3..12].
The public-preparation success premise remains explicit. These results reuse
the part-53 terminal proof; they do not claim it was missing before part 55.

J10753 composes the selected mask, extra coefficient lane, terminal call,
eta=sem[14] multiplication and both additions. Its output is exactly the
semantic model oracle at the actual point and coefficient tape. No assumed
terminal output or per-call oracle image remains. J10756 proves canonicality
of every prefix/sample/Boolean-tail point, constructs all 28×512 actual owned
oracle invocations, and feeds their outputs to partial sums and interpolation.
Its resulting polynomial is `PayloadSplit.rounds` of the complete oracle.
This eliminates the per-invocation `horacle` premise from J10705. It retains
canonical inputs, source prefix provenance, and successful public preparation;
it does not yet run the entire native semantic round driver or opening caller.

J10741 checks the extracted complete guarded encoder. J10748 joins its four
native stride-4 collections to the old generic channels. J10750 proves the
full optimized-node guarded eval/encode entry points equal to the old owner.
The encoder theorem requires successful canonical coordinate conversions to
justify a different pure operation order (channels before casts versus casts
before channels). Specialized used-method instances must discharge that premise.
J10739 adds literal canonical node-array equality on valid native indices.

All sixteen QM31 1024→256 lane/word collection checks now pass with full
allocation/collection, arbitrary raw inputs and arbitrary selected output
index. The four lane checks collectively cover every limb. All five actual
M31/QM31/WideExact constructor checks pass, including callback order and exact
raw outputs at lengths 4,9,10. All receipts record zero swap and unchanged caps.

Focused Poseidon native checks pass for local raw packing, both low folds,
external row arithmetic and complete internal linear transformation. The full
external transformation times out (181.108 s, 1063948 KiB); it is not retried
unchanged. Group/frame, column sums and finishing cuts replace that monolithic
gate. The whole frozen/candidate binding is still a separate obligation.

J10734/37/38 are rejected terminal qualification/transparency drafts;
J10742 is a point-model conditional draft; J10743 retires before invoking Lean
because a new carrier dependency is not yet compiled. J10745 needs a named
point model equality. J10747 replaces generic arithmetic reduction by explicit
list length facts. J10749/51/52 are rejected oracle drafts: result carrier,
namespace, duplicate alias/transparency and recursion-depth issues. J10753
uses named/opaque symbolic terms and raises no Lean limits. J10754/55 correct
an inferred power bound and an explicit finite-index cast. All failures remain
in the evidence; their `sorryAx` diagnostics are not accepted proof artifacts.

Accepted current-source checks (revision and dependency fingerprints are in
each JSON receipt; all printed axioms are subsets of the standard three):

| Attempt | Exact module | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| J10735 | R1Z.ProverCommitPoseidonCallable55 | 0 | 0:01.70 | 4140172 | 0 |
| J10736 | R1Z.ProverCommitComposition55 | 0 | 0:01.94 | 4203556 | 0 |
| J10739 | R1Z.ProverCommitNativeNodes55 | 0 | 0:02.30 | 4125484 | 0 |
| J10740 | R1Z.ProverCommitTerminalQName55 | 0 | 0:01.77 | 4243220 | 0 |
| J10741 | AspisR1ProducerRelease47.EncoderGuardComplete55 | 0 | 0:01.11 | 2637840 | 0 |
| J10744 | R1Z.ProverCommitTerminalCarrier55 | 0 | 0:01.71 | 4257448 | 0 |
| J10746 | R1Z.ProverCommitTerminalZero55 | 0 | 0:02.35 | 4261848 | 0 |
| J10748 | R1Z.ProverCommitGuardedChannels55 | 0 | 0:01.90 | 4102892 | 0 |
| J10750 | R1Z.ProverCommitGuardedAt55 | 0 | 0:01.67 | 4104752 | 0 |
| J10753 | R1Z.ProverCommitOracle55 | 0 | 0:01.91 | 4306240 | 0 |
| J10756 | R1Z.ProverCommitOracleRounds55 | 0 | 0:01.90 | 4305456 | 0 |
