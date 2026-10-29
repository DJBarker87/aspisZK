# LOG D481 / V373: compiled witness and pole kernel audit

**V373 remains OPEN. V380-inversion remains OPEN. Target not yet established.**
This is finite static evidence for one pinned client image, with explicitly
UNRESOLVED inline coverage and operand-provenance obligations. No confirmed
protocol-level FINDING is claimed. Two exact inversion zero branches are
identified; neither is dismissed as hardware trust or silently charged to a
new bad event.

Worktree `/Users/dominic/ZK/.worktrees/pv-l3a`, branch
`codex/pv-l3a-20261029`, base
`42760700cbae39587de93f520aed51618e13ef0a`. Host evidence directory:
`/home/dombarker/project-offloads/codex-pv-l3a-20261029/`.

## Frozen target / AGENTS section 6

Audited artifact: `tools/r1-cost-probe` release `devnet_spend`, SHA-256
**`fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348`**,
2,619,224 bytes; ELF64 x86-64 PIE, build ID
`75d113f47c57726e1aa91e512c5ba06abcbbad67`.
Read directly from the retained rdea build's `client-target/release/devnet_spend`;
its uninstrumented `client-deployed-baseline` has the identical hash. No binary
is committed. Addresses below are ELF virtual addresses before PIE relocation;
ranges are half-open.

Toolchain: rustc 1.94.1 (`e408947bfd200af42db322daf0fadfe7e26d3bd1`),
LLVM 21.1.8. Command/profile: `cargo build --release --locked`, `-j 4`,
`--bin devnet_spend`, features
`r1p-check,aspis-r1-cost-probe/ct-host-prover`; opt-level 3, default release
debug assertions/overflow checks off. No diagnostic debug rebuild is substituted
for this image. The reused build emitted LLVM IR/MIR using `RUSTC_BOOTSTRAP=1`
and a rustc wrapper; the separately retained baseline's identical hash prevents
confusing those diagnostic emissions with a different linked artifact.
Exact command/environment is in `reused-build-command.json`.

The build recorded source revision `713a92729abc0bb55677dd2ea7d2107490b5cd24`.
`source-parity.json` freshly compares all 567 listed project inputs plus five
build inputs against the assigned base: **572/572 match, none missing**.
This establishes listed-input identity across revisions, not a compiler theorem
or an independently complete dependency-source inventory. The host snapshot
omits `.cargo/config.toml`; the tracked file contains only an unused `xtask`
alias. The reused receipt explicitly records this, rather than claiming the
host contained that file. Lockfiles/manifests match. Protocol parameters and
wire format are those of these unchanged sources; no protocol or build source
is edited. Live deployment/installation attestation is not supplied by this
audit: this is the retained client artifact built in the deployed configuration.

`actual-feature-fingerprints.json` records 488 cached Cargo unit feature/profile
fingerprints, including build units and duplicate historical fingerprints;
these are not all runtime code. The selected project units record:

| Crate | Features |
|---|---|
| aspis-r1-cu-probe | private-leaf-salts, r1p-check |
| aspis-r1-cost-probe | ct-host-prover, default, private-leaf-salts, prover, r1p-check |
| aspis-prover | ct-host-prover, insecure-spend-fixture, prover, r0 |
| aspis-core | ct-host-prover, r0 |
| aspis-statement | pool-v1-kernel, r0 |

`reused-deployed-client-features.json` retains the earlier resolved dependency
feature graph for comparison; the observed fingerprints take precedence for
this cached build. CPU/OS/tool versions are in `host-platform.txt`: Intel Core
Ultra 7 155H, x86_64 Linux; GNU objdump 2.42. No CPU/MSR mode was changed.
**V371 remains substantive retained CPU-latency trust; DOITM remains pending
with the owner.** V370 compiler preservation and D381/D386 remain named,
retained obligations. Neither is discharged by this audit.

## Method and soundness limits

`PV_L3A_audit.py` reads all ELF function symbols and disassembles the linked
`.text`. It records 1,917 distinct sized symbol addresses (aliases retained),
12,296 resolved inter-function direct/GOT transfers, and 2,670 unresolved
indirect transfers. RIP-relative GOT targets are resolved through the ELF's
`R_X86_64_RELATIVE` relocations, rather than matching printed symbol names
alone. `calls.json`, `unresolved-indirect.json`, `function-index.json.xz` and
hashed `disassembly.txt.xz` preserve the inventory. These counts describe
linked code, not a proof of execution reachability from `action=prove`.

The local abstract interpreter joins register/flags/stack taints over the
syntactic CFG to a fixed point. It starts from secret M31 `rdi`, CM31
`rdi/rsi`, WideExact from-M31 `rsi`, and field operand memory loads for the
pointer ABIs. Argument addresses, lengths/layout and exponent arguments start
public, **conditionally on caller provenance**. Scalar aliases are merged;
flags propagate through arithmetic, tests, conditional moves and setcc.
Non-stack/non-RIP loads are conservatively secret. It flags tainted conditional
transfers, indirect targets, memory-address registers and division/selected
latency-review operands. Unsupported instructions and calls yield UNRESOLVED;
call return registers are overtainted. Complete per-body alerts, unsupported
instructions and seed descriptions are in `instances.json`.

This interpreter is an **unverified heuristic**, not a sound machine semantics
or noninterference proof. Stack spills are keyed by textual address, without
byte-overlap/stack-pointer alias analysis; partial SIMD-register writes are
not fully modelled; RIP-relative reads are treated public without a general
mutable-global influence proof; implicit control dependencies, exception paths,
speculation, microarchitectural state, dynamic libraries and callback ABI
composition are incomplete. This can miss dependencies as well as report
false positives. Consequently CLEAN means precisely **no secret-dependent
branch, address or selected variable-latency operation found by this finite
method under its seeds**, never universal absence. In particular the public
exponent assumption of the three pow bodies is not proved at every caller.

Seven local scanner controls pass (`controls.json`): secret branch, aliased
branch, secret address, indirect target, division, straight arithmetic and
unsupported-instruction rejection. These test the scanner, not the protocol.
Every linked conditional branch/indirect transfer/selected latency instruction
is retained in `whole-image-candidates.json.xz` (31,490 candidates), so an
absent kernel symbol is not mistaken for an absent inline copy. Unknown
instructions and CPU-specific latency outside the mnemonic list remain
unresolved under V371; integer multiply, cmov, SIMD and shift instruction
latencies are not certified here. This is not dudect evidence.

**Debug information obstruction:** `sections.txt` shows no `.debug_info` or
`.debug_line` (and no separate-debug link). Thus no requested source location
can honestly be reported *from this binary's debug information*. The source
locations below are source-informed associations, not DWARF results. No
compiler option or matching symbol name repairs this gap automatically.

## Instance table

For all rows, DWARF source location is **unavailable**. `field` means
`crates/aspis-core/src/field.rs`; `wide` means its `field/wide_exact.rs`;
`scalar` means `crates/aspis-core/src/r0/scalar.rs`; `semantic` means
`crates/aspis-r1-cost-probe/src/host_semantic.rs`. Source associations below
are candidates at the pinned source, not verified instruction/line mappings.
C = CLEAN under the method above; U = UNRESOLVED. F = confirmed FINDING;
no row qualifies as F without a checked witness/event provenance argument.

| Symbol/body | ELF range | Source association | Class | Resolved incoming sites |
|---|---|---|---|---:|
| host_semantic::build_with_material | 0x8ca20–0x8e4be | semantic:302 | U: aggregate ABI/callees | 1 |
| its closure #0 | 0x96060–0x9682e | semantic:327–340; inline pole candidate | U: aggregate ABI/callees | 1 |
| copy_tuple_limb | 0xbc480–0xbc4f2 | semantic:455 | U: public registry loads overtainted; width semantics | 10 |
| copy_endpoint_values | 0xbd1d0–0xbe149 | semantic:421–429; inlined compression candidate | U: public registry/secret trace separation and callees | 2 |
| M31::inv | 0x19b810–0x19c089 | field:213–234 | U: zero branch/panic call | 10 |
| WideExact::pow | 0x19c090–0x19ddfc | wide:163 | C, public exponent assumed | 10 |
| QM31::pow | 0x19ded0–0x19e6c3 | field:989 | C, public exponent assumed | 8 |
| QM31::try_inv | 0x19e6d0–0x19eba5 | field:1004 | U: zero branch/norm inverse | 7 |
| CM31::pow | 0x19ef10–0x19f0e0 | field:376 | C, public exponent assumed | 8 |
| qm31_m31_dot | 0x19fbc0–0x1a019b | field:1447 | U: unsupported SIMD/callee; loop alert needs public-length review | 0 |
| QM31 CodeField::add | 0x1a3740–0x1a3774 | scalar:26,70 | C | 7 |
| QM31 CodeField::mul | 0x1a3780–0x1a3c25 | scalar:35,70 | C | 9 |
| QM31 CodeField::sub | 0x1a3c30–0x1a3c6c | scalar:29,70 | C | 4 |
| WideExact CodeField::add | 0x1a3c70–0x1a3cd3 | scalar:26,87 | C | 3 |
| WideExact CodeField::mul | 0x1a3ce0–0x1a4d2c | scalar:35,87 | C | 3 |
| WideExact CodeField::sub | 0x1a4d30–0x1a4da3 | scalar:29,87 | C | 1 |
| WideExact CodeField::from_m31 | 0x1a4db0–0x1a4ddf | scalar:89 | C | 33 |

`kernel-call-sites.json` supplies **all 117 resolved incoming transfers for
these bodies**, each with caller name/range, target range, exact instruction
and site address. Every composed caller classification remains UNRESOLVED:
entry secrecy/public geometry has not been transported through the whole
client. Other register-indirect callers may exist; their precise unresolved
instructions are retained. The table is not asserted to enumerate every
compiled/inlined kernel instance.

The inline pole **candidate slice** 0x96520–0x9660c in closure #0 was also
manually traced (`pole-loop-review.json`; 52 instructions, machine-checked
sole branch). Chi is in xmm0–3; witness row values load at fixed offsets
0,16,32,48 through rdx. Public row rcx controls mask addressing and increments
by one; rdx increments by 64. Comparisons reduce through pcmpeqd/por/movmskps,
sete and `and %sil,%al`. The sole loop branch is `jne` at 0x96606, whose
flags come from `cmp %rcx,%r9` at 0x96603. No witness-position early exit was
found within this slice. This slice is CLEAN conditional on its public
address/length inputs; attribution to `ct_pole::all_slots_clear` is a
source/disassembly inference, not debug identification. The containing
function and its entry/predecessor argument provenance remain UNRESOLVED.

## Required scope coverage and inline gaps

| Design family | Coverage / exact unresolved reason |
|---|---|
| F1 pole row reader, tuple compression, equality/fold/scan | Two reader bodies and containing closure above; bounded scan slice above. `lean_copy_row_values`, `no_pole`, `ct_pole::{equal,keep_clear,all_slots_clear}` and both tuple compressor names have no standalone symbols. Missing DWARF prevents exhaustive inline-instance/source-span identification. |
| F2 M31 CT leaves, CM31/QM31/WideExact arithmetic and normalization | Seven CodeField bodies plus three pow bodies audited; scalar/tower arithmetic also occurs in callers and other linked functions. No complete inline inventory or compiler-origin map; CT leaf absence as a symbol gives no coverage credit. |
| Production trace/TLS removal | Design's source cfg claim retained. No new whole-client logging/trace absence theorem or binary-wide TLS elimination claim. |
| F3/F5/F6 challenge, private-coin, sparse/query/opening/checker paths | D166 joint simulatable-trace obligations retained, including failed prefixes and retries. Linked-image candidate inventory includes their machine code; witness independence of their arguments is not established by renaming them public challenges. |

D162 defines the L3 target; D166 does not turn challenge-dependent work into
unconditional constant time. The design's local source equivalences/two-run
claims and pv-l2d's model/helper results do not certify this image.
`pv-l2d/REPORT.md` explicitly leaves ten whole L2 rows OPEN and removes no
endpoint premise. This audit adds instruction selection, concrete branch
locations, GOT-resolved call sites and a bounded inline scan review for the
pinned client hash. It adds no source-equivalence theorem, whole-trace law,
compiler theorem or event-coupling theorem. Historical Kani claims are not
newly re-credited across the copy/function-pointer quarantines.

## V380-inversion: zero checks and every resolved call

`M31::inv` begins `test %edi,%edi` at **0x19b810**, followed by
**0x19b812 `je 0x19c06f`**, the panicking zero path. Source association:
`field.rs:216` assertion. Its secret, when witness-bearing, is the incoming
canonical field word in edi. The arithmetic continuation contains a fixed
addition chain; the entry branch is not constant time on unrestricted inputs.

`QM31::try_inv` loads its four operand limbs from rsi at
0x19e6de/0x19e6e0/0x19e6e4/0x19e6e8, ORs them into eax, then executes
**0x19e6f5 `je 0x19eb8f`**. That destination sets the Option discriminant
zero (`None`). Source association: `field.rs:1007–1008`. The tested secret is
the OR of all four operand limbs. The nonzero continuation calls M31 inversion
at **0x19e8fe** on the tower norm. Nonzero input implies nonzero norm only
with the correct canonical field/tower argument; that argument is not proved
by this machine scan. `WideExact::try_inv` has no standalone symbol and may
reach this same QM31 inverse on its norm. Its inline inventory is unresolved.

The following table enumerates **all 17 symbol/GOT-resolved inversion calls**
found across the complete image. No source location in this table is from
DWARF. `inversions.json`, `calls.json` and
`inversion-caller-disassembly.txt` retain exact caller ranges/instructions.
“Local nonzero” is finite static instruction evidence, not an end-to-end law.

| Call site(s) | Caller | Operand / assessment |
|---|---|---|
| 0xbe7d4 → M31::inv | host_sumcheck::interpolate, 0xbe6e0 | Source host_sumcheck.rs:17: product of distinct public i−j for 0≤i,j<28. Hence mathematically nonzero in M31; full machine provenance through interpolation helpers UNRESOLVED. Witness-bearing values are multiplied *after* this inverse. |
| 0x1111ce → M31::inv | z4 z9c::emit closure, 0x110790 | edi loaded from matrix at `(%rax,%r14,4)` immediately before call. Matrix/guard provenance and joint F6 law UNRESOLVED. |
| 0x116674 → M31::inv | z4 z9c::TagEch::insert, 0x116480 | edi from ebx. z9c.rs:112–130 skips v[i]=0 before inversion; association of this pivot to machine predecessors and complete influence law UNRESOLVED. |
| 0x1223e9 → M31::inv | z9b::rp_dual_fold, 0x1223c0 | `mov $4,%edi` at 0x1223e4: local nonzero. Source z9b.rs:59. |
| 0x1247d4 → M31::inv | z9b::pair_fold, 0x1247a0 | `mov $2,%edi` at 0x1247cf: local nonzero. Source z9b.rs:51. |
| 0x128224 → M31::inv | z9c::chain_targets, 0x128050 | `mov $2,%edi` at 0x12821f: local nonzero. Inlined normalization source attribution unresolved. |
| 0x128e7c → M31::inv | z9c::emit, 0x128e60 | `mov $2,%edi` at 0x128e77: local nonzero. Source z9c.rs:340. |
| 0x13a58a → M31::inv | z9e::public_data, 0x132100 | `mov $4,%edi` at 0x13a585: local nonzero. Inlined source attribution unresolved. |
| 0x175f1e → M31::inv | PairLeafWitnessV1::two_outputs, 0x175e60 | Sentinel from second commitment lane 7, source pair_tree_profile.rs:214–221. `test edi,edi` at 0x175f0d; `je 0x175fa4` at 0x175f0f returns OccupiedSentinelZero before the call. No intervening write to edi on this straight-line continuation. Local inverse input nonzero; privacy/charging of the earlier witness-dependent rejection prefix is UNRESOLVED. |
| 0x19e8fe → M31::inv | QM31::try_inv, 0x19e6d0 | Norm inverse, source field.rs:1011 through CM31::inv at :390. Canonicality/norm-nonzero transport UNRESOLVED. |
| 0x1282a0 → QM31::try_inv | z9c::chain_targets, 0x128050 | Inlined normalize_d on challenge coordinates; source z9c.rs:227. Joint challenge provenance/nonzero event containment UNRESOLVED. |
| 0x128f22 → QM31::try_inv | z9c::emit, 0x128e60 | a[9]−1/2, source z9c.rs:341. Zero returns HalfOK failure; hidden-attempt challenge/event containment UNRESOLVED, not labelled witness-independent merely because named a. |
| 0x162453, 0x1625a1, 0x16270f, 0x1628bb → QM31::try_inv | host_forest::build_pool_v1_pair_forest_copy_helper_v1, 0x1622a0 | Four unrolled producer/consumer slots, source crates/aspis-prover/src/host_forest.rs:890,902. Operand chi−compressed witness tuple. Source no_pole guard at host_semantic.rs:329 precedes helper call at :332 on the selected path. Zero implies an active pole *if* registry/static-slot correspondence, canonical field subtraction and reached-caller binding hold; complete compiled-path proof to the already-charged event remains UNRESOLVED. |
| 0x1a04ea → QM31::try_inv | secure_circle_point_from_parameter, 0x1a01a0 | 1+parameter², circle.rs:41. SingularParameter error is explicit. Parameter/challenge provenance, subfield exclusion and joint event containment UNRESOLVED. |

The helper caller constructs each denominator in SIMD before the inverse;
for example 0x16241b–0x162443 subtracts the producer value from chi and
stores the operand, 0x162453 calls the inverse, and 0x162459/0x162461 tests
its Option discriminant before the CopyImbalance error path. Thus the
zero check is actually present in the audited image, not inferred solely
from Rust. The other three exact calls and their discriminant branches are
in the saved caller disassembly.

**No new charged event is introduced.** The source implication “NoPole ⇒
active denominator nonzero” is a conditional mathematical/source argument;
this audit does not instantiate its same-run native/refinement hypotheses or
prove its failure probability. A reachable witness-dependent zero outside
those events would be a protocol-level FINDING. We have not exhibited such
a run, so the two observed operand-sensitive branches are UNRESOLVED rather
than falsely declared either harmless or exploitable.

`source-inversion-candidates.json` retains 298 regex hits over the pinned
source superset, including tests, inactive cfg code and other functions.
They are a checklist, not 298 reached inversions. Optimizer inlining, constant
folding and unresolved register-indirect paths prevent proving the symbol
call list is every inversion on every witness-bearing path. That is the
precise residual for the requested universal inversion statement.

## Receipts, validation and premise accounting

One new capped native **analysis** scope, zero Rust compilations, zero Lean
attempts, zero Kani. All IDs 68100–68199 (including audits 68197–68199) remain
unused. No failed-source Lean wrapper exists; ruling (u)'s wrapper guard is
therefore not invoked. No extraction, stdlib/model binding or singleton
harness credit is claimed; own-1, final own-2''' and x' are not replaced by
machine-code resemblance. No source under crates/ or programs/ changed.
No wallet, key, account, fund, external message, publication or push operation.

| Gate | Exact evidence / target | Exit | Wall | Peak RSS | Swap | Revision / axioms |
|---|---|---:|---:|---:|---:|---|
| native01 | `native01-receipt.json`, linked image inventory + CFG taint; exact command in receipt | 0 | 7.087 s | 341,168 KiB GNU-time; cgroup 370,216,960 bytes | 0 | assigned base 42760700cb; `#print axioms`: N/A, no theorem |
| Reused release build04 | `reused-build-command.json`, `reused-build04-time.log`; unchanged client artifact, not rerun | 0 | 16.42 s | 457,604 KiB GNU-time | 0 | 713a92729a; listed source parity checked to base; axioms N/A |
| Local finite controls/provenance/supplement | `controls.json`, `source-parity.json`, `pole-loop-review.json` | 0 | not a formal release result; resource timing not recorded | not recorded | not measured | base pinned by scripts; axioms N/A |

`native01-admission.json` has allowed:true and exit 0 was checked in the
same command/process that launched the scope. Scope limits were read back:
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. One scope at a time;
no refusal, cooldown violation, failed/killed rerun or cap increase occurred.
Launcher SHA-256:
`40016f3858548f2f8272e904f6846d37f14f7c59b607240a7540dc4d1dee9eda`;
audit script SHA-256:
`48d4f79566d6f201f21cb8b2bd4c885f68027e45229d8d2d24aa190dfbc6317f`.
The retained build's original cap/source receipts remain at
`evidence/pv-rdea-20261028/`; this job reuses its artifact without rebuilding
or writing into its workspace. Initial host inspection commands were
read-only file/symbol/provenance inspection, not release gates; their resource
usage was not measured. No formal manifest replay was applicable or run.

Before/after: **V373 OPEN/P → OPEN/P**, now with concrete finite binary
inspection evidence and explicit coverage gaps; **V380-inversion OPEN/P →
OPEN/P**, now with exact zero branches and 17 resolved call sites. **V367**
source/caller composition retained; **V370**, **V371**, DOITM and the
D381/D386 boundary retained. No headline premise removed, added, widened or
folded into T. T remains exactly entropy_law, entropy_kernel, observation;
no new trust field. The simulator, observer, bad-event list and protocol are
unchanged. No whole-program constant-time, privacy or 100-bit claim follows.

This completes the available-image classification deliverable with unresolved
cases, rather than consuming compiler budgets on unrelated proofs or repeated
unchanged scans. The next concrete deliverable is a source/inline-origin map
for **this exact linked text** (original matching DWARF or a separately proved
text-identical debug companion), followed by a compiled call-site argument
transporting NoPole and canonical norm nonzero to the same already-charged
events. Until then, exhaustive inline coverage and universal inversion safety
remain unestablished.
