# LOG D484 / V373 and V380-inversion

**V373 OPEN → OPEN; V380-inversion OPEN → OPEN. Target not yet established.
No endpoint premise removed, added, widened, or folded into trust.**

Branch `codex/pv-l3b-20261029`, candidate
`b3a9a2842fe8104e5a20268990ddd9a52517bf80`, same sparse worktree
`/Users/dominic/ZK/.worktrees/pv-l3a`. Host directory:
`/home/dombarker/project-offloads/codex-pv-l3b-20261029/`.
This continuation used **39 new capped native scopes**, native02–native40;
with inherited L3A native01 this exhausts **40/40**. Zero Lean attempts,
zero Kani; IDs 68400–68499, including audit IDs 68497–68499, remain unused.
Existing nonzero proofs were inspected and cited instead of recompiling
unchanged theorems. No crates/programs change, push, deployment, key cleanup,
fund operation, or external message occurred.

## Debug provenance: the requested experiment

The audited baseline remains SHA-256
`fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348`.
The release-with-DWARF companion is
`a0f91ec9ed2c29a9373e8ac44454a35e8c48e41894c969ca998bd15134ed9976`.
**They do not have identical `.text`. DWARF is used ONLY AS A GUIDE.**

`debug-build-command.json` records the original cargo command verbatim:
`cargo build --release --locked`, package aspis-r1-cu-probe, bin devnet_spend,
features `r1p-check,aspis-r1-cost-probe/ct-host-prover`, -j4, CPUs0–3,
rustc 1.94.1, same source workspace, Cargo.lock, and emission wrapper.
The sole codegen-setting change is `CARGO_PROFILE_RELEASE_DEBUG=2`.
Release optimization remains 3, debug assertions/overflow checks remain off,
and strip remains its default none. The new target directory is task-owned;
the baseline and other jobs' caches were not overwritten. Time is spent in
compilation/DWARF emission, not proof generation or elimination.

`source-parity.json` compares the candidate against the retained build's
567 source plus five build inputs: **572/572 identical**. The original build
revision is 713a92729abc0bb55677dd2ea7d2107490b5cd24; this is listed-input
identity, not an independently complete source inventory or compiler theorem.
`build-input-hashes.json` pins lockfile, manifest and wrapper. The wrapper
retains RUSTC_BOOTSTRAP=1 and the same LLVM/MIR emission flags.
`configuration-fingerprints.json` records all 488 baseline and 487 diagnostic
cached unit fingerprints, their resolved features and profiles; every recorded
`rustflags` array is empty. Both RUSTFLAGS environment variables are unset.
Historical duplicate fingerprints are not counted as reached runtime units.
The host snapshot's absent `.cargo/config.toml` and its unused tracked xtask
alias remain as disclosed in L3A. No changed build source is substituted.

| Section | Baseline | Debug companion |
|---|---|---|
| `.text` VA | 0x67370 | 0x67310 |
| `.text` bytes | 1,771,904 | 1,772,096 |
| `.text` SHA-256 | `054a11af1afc3ff8b7fa0380486cf1499ae85b4b533c77b5478152ca94a98a26` | `a1d30e0704889d6175ce20d921886b0e8d7b2be9312717ff92de73f0100c40ef` |

At equal section offsets, **1,628,299 bytes** differ across **65,767 maximal
intervals**. `text-difference-intervals.json.xz` records EVERY interval, with
both section bases and the unequal-length suffix; it is an offset comparison,
not an instruction alignment. First interval [27,28), at baseline VA 0x6738b
and companion VA 0x6732b. `symbol-address-comparison.json` records every named
function's original and companion address/size lists: zero of 1,716 named
entries have identical address lists. The full nm outputs are retained.

All 17 selected kernel bodies have equal instruction sequences under the
recorded relocation-masking heuristic (`native05`–`native21`). This is useful
finite supporting evidence, **not byte identity**. The heuristic masks direct
transfer targets and RIP-relative relocations; it cannot establish equal
referents, identical data, or compiler preservation. Companion addresses are
never passed to addr2line as though they were baseline addresses.

## Inline inventory and exact limits

`native04` traversed all CUs and DIEs: **728,638 concrete function/inline
records**; full ranges, source lines, call lines, parent origins and DIE IDs
are in `dwarf-all-instances.json.xz`. This is exhaustive over emitted records,
not proof that optimized DWARF preserves every source origin. `native39`
selects a conservative kernel-origin superset and maps equal masked function
instruction sequences back to the baseline. `inline-kernel-guide.json.xz`
retains every selected record and every mapped/unmapped instruction address.

| Origin family | Concrete diagnostic records |
|---|---:|
| Field source, including arithmetic leaves/towers | 127,922 |
| WideExact | 1,157 |
| CodeField | 280 |
| F1 readers/caller | 34 |
| F1 pole equal/fold/scan | 3 |
| F1 tuple compressors | 2 |

Total **129,398** selected origin records; **345** have an instruction not
mapped by the whole-function heuristic. It compares 1,603 unique named
function pairs and finds 1,589 equal under masking. Ambiguous duplicate-name
functions and changed sequences remain unmapped. These are explicit gaps,
not absent-kernel conclusions. `whole-function-alignment.json` identifies
every compared range and result. `F1-inline-summary.json` supplies individual
F1 DIE/range/call-line entries: one each no_pole, lean_copy_row_values,
all_slots_clear, keep_clear, equal, copy_endpoint_values, copy_tuple_values,
compress_tagged_tuple, compress_tuple; seven copy_tuple_limb records (one
out-of-line and six inline), 21 optimized copy_cell records, and two caller
records. Record counts are compiler-origin counts, not semantic source-call
multiplicity: vectorization and coalescing can merge origins.

Per-body guides retain all overlapping DIEs and addr2line inline stacks at
EVERY companion instruction (`native05`–`native21` detail/lines/disassembly).
Per-inversion guides do the same for all 17 compiled callers, including the
complete predecessor context (`native22`–`native38`). Some per-caller
"changes" are conservative display-normalization artifacts: stripping `#`
also truncates demangled `{closure#0}` names, leaving a different address.
The native39 whole-image mapper corrects this by recognizing only objdump's
whitespace-delimited comment marker. No body is rerun to obtain a verdict.

**The requested universal identification of EVERY shipped inline copy remains
UNRESOLVED.** A different-text companion plus masked alignment does not
establish it. This run resolves source-origin ambiguities in the diagnostic
image and gives exact finite baseline candidate maps; it does not silently
promote those into exact shipped DWARF or a complete compiler-origin proof.

## Review of the seven formerly UNRESOLVED bodies

Addresses below are the BASELINE half-open ranges. Source associations now
come from the companion guide plus the recorded instruction mapping.
`C` means only finite local CLEAN under the specified ABI/provenance inputs;
`U` remains an exact open obligation. No unconditional whole-caller closure.

| Body / baseline range | Source guide and resolved local behavior | Class / precise residual |
|---|---|---|
| build_with_material 0x8ca20–0x8e4be | host_semantic.rs:302; clone_semantic_columns :346, build_with_helper_mode :51, check_base_column :157, check_secure_column :166 inline | **U**. Public-statement/shape checks and cloning identified, but canonicality rejection reads operand words. Must prove reached C1/d/g words canonical and bind challenge-driven sparse/callee work to the same joint trace. Neither DWARF nor source validity names discharge this. |
| closure #0 0x96060–0x9682e | :327 → no_pole :361 → lean_copy_row_values :402 → ct_pole.rs:18/14/5 | **U** containing caller. The vectorized scan's sole loop branch 0x96606 uses public row count; verdict branch chooses ActivePole. Registry construction/read bounds, helper composition, same-run slot correspondence and existing charged-pole event transport remain obligations. Scan slice remains local **C** under public shape/masks. |
| copy_tuple_limb 0xbc480–0xbc4f2 | :455, copy_cell :470, stable/late calls :463/:464 | Local **C** conditional on public descriptor and shape. Branches 0xbc485/497/49f/4ad/4be/4c9 test enum/bank/column/row bounds. Witness load is 0xbc4d4; arithmetic afterward is lea/cmp/cmovb/store, no conditional transfer or witness-address use. Must bind supplied descriptor and vector lengths to registry/public geometry at callers. |
| copy_endpoint_values 0xbd1d0–0xbe149 | :421; copy_tuple_values :433, six inline limb reads, ten out-of-line limb calls, compressor origins | Local **C** under public row/side/slot/arity/descriptor/layout. Bounds/error transfers are metadata-dependent; witness limbs enter fixed arithmetic compression, then the public slot store. Full caller composition/public geometry and allocator/error boundary remain **U**. |
| M31::inv 0x19b810–0x19c089 | field.rs:213/216 | Unrestricted **U**, precisely zero branch 0x19b812 to panic. Nonzero continuation is fixed addition-chain arithmetic. Each of ten incoming calls is accounted below; conditional norm/pivot/initializer bindings are still required. |
| QM31::try_inv 0x19e6d0–0x19eba5 | field.rs:1004/1007; inlined CM31::inv :391, inv_with :398 | Unrestricted **U**, precisely whole-value zero branch 0x19e6f5. Seven incoming calls below; canonical norm-nonzero transport required for nested M31 inverse. Nonzero arithmetic continuation has fixed field operations. |
| qm31_m31_dot 0x19fbc0–0x1a019b | field.rs:1447 | Local **C** under public slice pointers/lengths/layout. All conditional transfers select public length mismatch, <=4 shape, public loop/tail counters or end bounds. paddq is fixed SIMD addition; xchg ax,ax is a register nop. Witness data enters multiply/add/reduction, not the address/control counters. Panic call is only the public length mismatch. Complete reached-caller shape and V371 latency remain obligations. |

The local manual reviews repair specific scanner overtaint/unsupported-op
ambiguities, not the scanner's soundness. Original L3A unverified taint
interpreter limits, stack/SIMD alias gaps, hidden globals, implicit control,
speculation and indirect call composition remain. Finite instruction review
does not prove noninterference. Pointer/layout/public-registry assumptions
are recorded as obligations, not newly adopted endpoint hypotheses. V367,
D162/D166, pv-l2d whole-source/caller and joint-trace obligations remain.

## V380-inversion: all 17 calls and both zero branches

`zero-branch-guide.json` associates **0x19b812** with field.rs:216 (M31 zero
panic) and **0x19e6f5** with field.rs:1007 (QM31 None). Companion sites are
0x19b852 and 0x19e735. Each branch lists all ten/seven incoming sites,
respectively. The following source lines are guide associations, not DWARF
from the deployed binary. `call-proof-obligations.json` retains complete
inline stacks, mapped companion sites and exact obligations for EACH call.

All theorem names below have prefix `R1Z.`. Statements and candidate source
hashes are in `existing-proof-inventory.json`; `reused-inv-AXIOMS.md`, audit
manifest and summary retain the historical successful proof/axioms evidence.
These are existing conditional results, not new deployed-code proofs.

| Baseline site → inverse | Source caller, including inline parents | Existing result / exact obligation |
|---|---|---|
| 0xbe7d4 → M31 | host_sumcheck.rs:17 interpolate | `PV_Inv_InterpolationSource.source_inverse_operand`: bounded i<28 initializer has canonical nonzero denominator and successful inverse. Bind actual initializer and loop bound to the owned extraction; witness interpolands do not enter this denominator. |
| 0x1111ce → M31 | z9c.rs:42 invm ← :309 invert ← :711 emit_lifts ← :357 emit worker closure | `PV_Inv_Pivot.selected_nonzero/selected_inverse` is a generic selection theorem. Bind find(nonzero), swap and the subsequently loaded a[c][c] with canonical matrix invariant; preserve complete F6 challenge history. |
| 0x116674 → M31 | z9c.rs:42 invm ← :126 TagEch::insert | Same pivot/guard results; bind `v[i]==0` continue to actual loaded pivot across row updates and preserve canonicality/F6 history. |
| 0x1223e9 → M31 | z9b.rs:59 rp_dual_fold | Immediate 4 in edi: finite local nonzero. `PV_Inv_Guard.nonzero_branch` applies to nonzero field values; no witness-zero event needed. |
| 0x1247d4 → M31 | z9b.rs:51 pair_fold | Immediate 2, same local conclusion. |
| 0x128224 → M31 | probe.rs:2291 normalize_d ← z9c.rs:225 map closure ← :227 chain_targets | Immediate 2, same local conclusion; previously unresolved inline origin identified. |
| 0x128e7c → M31 | z9c.rs:340 emit | Immediate 2, same local conclusion. |
| 0x13a58a → M31 | z9b.rs:108 design_relations ← z9e.rs:80 public_data | Immediate 4, same local conclusion; previously unresolved inline origin identified. |
| 0x175f1e → M31 | pair_tree_profile.rs:221 two_outputs | `PV_Inv_Sentinel.nonzero_success/zero_reject`. test/je at 0x175f0d/0x175f0f guards edi with no intervening write. Bind native constructor/reference and prove joint law of earlier witness/coin-derived zero rejection. Guarded inverse alone does not cover that prefix. |
| 0x19e8fe → M31 | field.rs:398 CM31::inv_with ← :391 CM31::inv ← :1011 QM31::try_inv | `PV_Inv_NativeNormQ.norm_operand` + `PV_Inv_NativeNormC.norm_operand`: both actual extracted norm operands are nonzero from canonical nonzero input. Transport actual canonical input and norm arithmetic to this same native call. |
| 0x1282a0 → QM31 | probe.rs:2292 normalize_d ← chain_targets closure :225/:227 | alpha[9]−1/2. `PV_Inv_Guard.difference` characterizes zero; no universal native nonzero theorem identified. Prove exact challenge provenance and failure-prefix simulation/containment on headline coupling. |
| 0x128f22 → QM31 | z9c.rs:341 emit | Same half-pole denominator; same exact outstanding challenge/failure-prefix obligation. A challenge name is not a joint-law proof. |
| 0x162453 → QM31 | host_forest.rs:890 producer slot 0 | `PV_L2_InversionPole.producer`, `PV_Inv_NativeRegistry.producer`, `PV_Inv_NativePackScan.guarded_packing`; bind registry/tag/trace tuple, active row, packed slot and native no_pole guard on SAME run, then existing pole-charge containment. |
| 0x1625a1 → QM31 | host_forest.rs:890 producer slot 1 | Same producer results; distinct compiled slot/canonicality binding required. |
| 0x16270f → QM31 | host_forest.rs:902 consumer slot 0 | `PV_L2_InversionPole.consumer`, guarded packing; corresponding consumer slot/input and event bindings required. |
| 0x1628bb → QM31 | host_forest.rs:902 consumer slot 1 | Same consumer results; distinct compiled slot binding required. |
| 0x1a04ea → QM31 | circle.rs:40 secure_circle_point_from_parameter | 1+t². `PV_Inv_Circle.singular_iff/denominator_nonzero`, `PV_Inv_CircleSubfield.outside_subfield_safe`. Bind actual sampler/subfield exclusion, raw candidates and fallback jointly to headline history. Without that domain restriction ±i are zeros; no unproved charge is assigned. |

`PV_Inv_NativeQ` and `PV_L2_InversionQ.branch_nonzero/logup_operand/zero_exact`
also give the canonical extracted whole-value branch and inverse laws. The
existing charge is **8·4096/((2^31−1)^4−1)** in
`PrivacyR1Final.modelError`, as formalized by PV_Inv_PoleMass/PoleUnion and
BadContainment/ChargeRules; it is not a seed/fuel/fresh-budget charge and is
not multiplied again by the number of native calls. Native same-coupling
containment remains unproved. No new bad event or changed probability bound.

**No checked reachable witness-dependent inversion-zero outside the existing
event has been exhibited; no protocol-level FINDING is claimed.** This is
not a proof of its absence. Zero-sensitive half-pole/circle calls and sentinel
rejection require the exact joint laws above. The four witness-denominator
calls retain registry/slot/NoPole binding obligations. Unresolved indirect
transfers and unmapped inline origins prevent asserting that the 17 resolved
calls are every inversion on every reached witness path.

## Receipts, boundaries and stopping condition

Each nativeNN receipt has exact target command, exit, wall, cgroup peak,
swap, source revision and axioms=N/A; its GNU-time log gives process peak
RSS. Admission JSON AND exit were checked in the same launcher process before
each scope. Caps read back: MemoryHigh=6 GiB, MemoryMax=8 GiB,
MemorySwapMax=0, TasksMax=64. One scope at a time. All 39 new exits are zero;
no refusal, cooldown violation, killed job, failed-source rerun or cap raise.
`native-receipt-index.json` indexes native02–39; native40 has its separate
receipt. `RUNS.md` consolidates all 39. Native02 build wall 138.199 s,
cgroup peak 6,442,913,792 bytes; native04 traversal wall 126.297 s,
cgroup peak 5,194,293,248 bytes. All new swap observations and GNU-time swaps
are zero. No new theorem/axioms audit or full frozen manifest replay applies.
The final gate checks all 17 call mappings, both branches, prior receipts,
cap/admission invariants and empty RUSTFLAGS fingerprints. Pyelftools 0.32
was installed task-locally; install log retained. No external tool files are
committed. Large text/JSON artifacts use xz plus uncompressed SHA-256.
All 39 new scopes total 535.006 seconds; maximum GNU-time process peak RSS
is 5,047,912 KiB. `all-native-receipts.json` and `FINAL-VALIDATION.json`
record the final local receipt/hash/size checks. The 108,568,136-byte DWARF
binary is retained on the host as `debug-client-retained`, with identical
hash recorded in `artifact-retention.json`; only this task's rebuildable
Cargo cache was removed. The original command paths in receipts are historical;
to repeat analysis, use the retained binary in place of the old target path.
No binary or compiled object is committed.

The native budget is exhausted; Lean is unused because this task's next
missing statements are concrete code-origin/caller/event bindings, not a new
generic inverse lemma. We do not spend theorem attempts recompiling unchanged
conditional results or claiming their hypotheses as conclusions. No endpoint
premise has been removed. V370 compiler preservation and D381/D386 remain
named obligations; V371 CPU data-independent latency remains substantive
retained trust and DOITM remains pending with the owner. T remains exactly
entropy_law, entropy_kernel, observation. simE, observer, protocol, release
pins and bad-event union are unchanged. No whole-program CT, privacy or
100-bit security claim follows.

Next concrete deliverables: (1) the original matching DWARF/object origin map
for fa888460, or a checked origin-preserving mapping covering ambiguous and
changed functions and the 345 unmapped origins; (2) native registry/packed-slot
and canonicality bindings instantiating the existing inverse proofs on the
headline coupling; (3) certificate/circle/sentinel joint failure-prefix laws.
These remain exact obligations, not hardware-trust substitutions.
