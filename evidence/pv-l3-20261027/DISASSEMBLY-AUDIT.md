> Latest D269 resume: see [two-artifact audit](dual/AUDIT.md),
> [checked sites](dual/findings.json), and [V374 plan](dual/V374-PLAN.md).
> A (5228877938) built with the devnet R1 recipe, toolchain unpinned (host default
> rustc 1.94.1), SHA256 dc31d28c3eb9a793f9e2a8c81e69611b42aa8c2cace1393845cd554d090c357b.
> B (237e135561) failed `--locked` before compilation: no B executable or addresses.
> New A finding: non-CT pole limb-prefix branches `0xbd6a0/0xbd6a6/0xbd6ac`,
> separate from D268's final poleBad verdict. V373/V374 remain OPEN; the complete
> two-artifact audit is unfinished. Earlier sections below are retained history.

# V373 compiled-kernel audit — 2026-10-27

Status: checked candidate findings; shipped source/entry identified, exact build recipe pending, deployed V373 OPEN. Target not yet established.
This is static native evidence, never a proof of absence of leakage. V374 timing
is a separate task. No implementation changes are authorized or made.

## Stage 1: identity and scope

Assigned branch `codex/pv-l3-20261026`, initial HEAD
`3d19f820c9585aba89f267e05637c0705744703d`. Its crates, Cargo manifests/lock and
configuration are byte-identical to candidate ancestor
`619e192e0a6d940a3291319b2ce3ddc941854fe4` (empty path-restricted git diff).
`source-pins.json` records the exact current build inputs. No current research
source is silently substituted for this candidate.

Read common rules (a)–(k), corrected (h'), restoration flag, root AGENTS security
and proof discipline, D162/D167 and research D244–D248 (Stream B). Research read
snapshot `2efd18ec4e97d838a6cfe750384f158b0e58636a` supplies the separately
attributed `inversion-inventory-research.md`; that inventory's baseline is
`9c4bfcc830c09f8d85fd1ed7996f8d9dcf059c84`, so all included edges require checking
against this job's pinned source. No Lean module or shared object is modified.

D162 names a platform and a route, not an executable. The candidate's
`aspis-r1-cost-probe` is a library (`src/lib.rs`: “no production entrypoint”).
`RealR1_client::prove_for_proof_accounts` is generic over the account callback.
The earlier collector's `pv-l3-evidence` executable is explicitly evidence-only
(design/PV-L3-20261026.md), with extra named wrappers and fixture callers.
Its SHA256 `4735ed37062fef000af06563a1661767a9142884f4439abfecd9557f4a61da58`
cannot be presented as the shipped binary. Shipping entrypoint/features/flags/
toolchain have been requested. Until supplied, a candidate example build can
only provide supplementary findings, not an exact deployed V373 result.

For supplementary inspection use the existing unmodified `r1p_retry_gate`
example: unlike the earlier wrappers it reaches the real retrying prover with
OS entropy, but it is still a diagnostic fixture executable, not a deployed
proof-account client. Build only, never execute it. Reuse the assigned host
workspace/cache; check every pinned build input before launch. Expected time
is compilation/linking, no proof generation, elimination or timing tests.

## Kernel inventory to resolve in the compiled binary

| Family | Pinned source / callers | Required review |
|---|---|---|
| CT field reducers and M31/CM31/QM31/WideExact arithmetic | `aspis-core/src/field/ct.rs`, field.rs, field/wide_exact.rs; semantic compression, mask balance, dot/evaluation callers | inline instances, reductions, selection, multiply, public-exponent loops |
| Witness tuple readers and pole handling | host_semantic.rs::copy_tuple_limb/copy_cell/copy_endpoint_values/no_pole → ct_pole.rs::all_slots_clear → build_with_material closure | descriptor-index provenance, full scan, final pole-verdict branch |
| Tagged compression and inverse helper | statement/logup.rs::compress_tagged_tuple/build_state_only_copy_logup_helper → semantic_oracle.rs/pair_forest_trace.rs | actual inlined operations, inverse zero/Option boundaries |
| Mask construction / balancing / seed expander | prover/state_only_hiding.rs and core/state_only_hiding.rs; StateOnlyAttemptSecrets material builder → prover::prove_masked_with_attempt | private-seed rejection, balance coordinates and memory addressing |
| Entropy comparisons | state_only_entropy.rs::entropy_nonzero32/generate/generate_for_mask_nonce | comparison lowering, short circuit and zero rejection; public nonce distinct from private seeds |
| FS sampler / rejection | cost-probe/sampler.rs, host_transcript.rs, core circle.rs | constant-divisor lowering; gamma carry; circle fallback; query duplicate control |
| Public interpolation inversions | host_sumcheck.rs::interpolate | denominator fixed by public i,j, despite witness-derived polynomial values |
| Honest compiler envelope | statement/pool_v1/pair_forest_copy_builder.rs::inv_r; pair_tree_profile.rs constructor sentinel | constant remainder lowering, zero sentinel and witness-derived predicates |

CPU DOITM is OFF under D248: no data-independent latency guarantee is inferred
for non-DIV instructions either. Record operand-dependent ALU/multiply/SIMD/
compare/select/shift operations as depending on V371; DIV/IDIV, if present, need
explicit operand provenance. No new T field or implicit native assumption.

## Stage 2: supplementary candidate binary built and extracted

Exact command in the reused host `src/` (no executable run):

```sh
CT_EXPECTED='optimized compilation and linking of existing retry example only; no execution, proof generation or elimination' \
python3 tools/ct-kernels-20261022/run-host.py l3-audit-build-001 \
  cargo build --release --locked --offline -j 4 -vv \
  -p aspis-r1-cost-probe --features optimized-terminal,ct-host-prover \
  --example r1p_retry_gate
```

Runner sets `RUSTFLAGS='-C link-arg=-Wl,--threads=4'`, `CARGO_BUILD_JOBS=4`,
`CARGO_NET_OFFLINE=true`, and the existing `../target` cache. Native default
`x86_64-unknown-linux-gnu`, no target-cpu override. Cargo release defaults:
opt-level=3, codegen-units=16, LTO=false, strip=debuginfo, debug assertions off,
overflow checks off except the root's certificate checker/build overrides.
Resolved features and actual rustc command lines are retained in
`receipts/build/stderr.log`; this is the feature identity of this example only.

Built executable SHA256
`c7f359d4da1c5a759a3ddf4b83c7cccd602b9e0c104e85170a593f82116b516a`,
2,757,008 bytes. rustc 1.94.1 commit
`e408947bfd200af42db322daf0fadfe7e26d3bd1`, LLVM/LLD 21.1.8;
GNU objdump 2.42. Identity and ELF comment: `disassembly/identity.json`.
All 1,067 pinned source/configuration files, including three extracted-builder
path dependencies, byte-match host inputs (`audit-source-comparison-20261027.json`).
The reused host's historical `source-revision.txt` still says `b07624802f…`;
the receipts retain that fact honestly. The file-by-file comparison binds the
compiled inputs to initial HEAD `3d19f820c9`; no historical receipt is rewritten.

Two sequential 6G/8G/swap0/Tasks64 scopes: release build exit 0, 67.075 seconds,
566,628 KiB maximum process RSS, swaps 0; extraction exit 0, 2.866 seconds,
245,880 KiB RSS, swaps 0. Raw cgroup peaks, limits and full commands are in
`receipts/{build,extract}/receipt.json`. `#print axioms`: N/A (no Lean).
Reservation receipts retained; the first preflight addressed a nonexistent
prover-rw script in this reduced workspace and launched no scope. The second
used the existing CT collector's reservation script; no infrastructure changed.

Extraction runs `nm -S -n -C`, `objdump -d -C -Mintel --no-show-raw-insn` and
`readelf -rW` against the built ELF under its own scope. 163 selected symbols,
28,232 instructions, 569 statically resolved incoming call/tail-jump sites.
Selection deliberately includes support/drop code; neither these counts nor a
lack of DIV is an audit verdict. `call-sites.json` resolves RIP-indirect calls
through ELF RELATIVE relocations; runtime function-pointer targets are not
claimed complete. Full disassembly remains on the owned host; selected text,
symbols, relocations and extraction script are retained here.

## Stage 3: checked instruction-level findings

All addresses below are link-time virtual addresses in **only** binary
`c7f359d4da1c5a759a3ddf4b83c7cccd602b9e0c104e85170a593f82116b516a`.
PIE load bias must be added for runtime addresses. Endpoints are exclusive.
“Clean in body” means no secret-dependent branch/address or secret DIV was
identified in the specified reviewed body under the stated input conditions;
it is an audit observation, not absence of leakage. Every arithmetic row still
depends on V371. No “clean” verdict transfers to an unreviewed inline copy.

### Findings requiring explicit retention

| ID / kernel | Instruction and source | Operand provenance / finding |
|---|---|---|
| F1 — private mask rejection, inlined `SeedExpander::m31` in `qm31` | `0x16f5af mov r13d,[r15+rdi]`; `and r13d,0x7fffffff`; `0x16f5bd je 0x16f676`. `crates/aspis-prover/src/state_only_hiding.rs:424–426` | **CHECKED secret-dependent branch.** r15 is the private seed-derived hash block, rdi its current byte offset. Candidate P is rejected, every smaller candidate accepted. Other limbs have equivalent branches at `0x16f6bd`, `0x16f7bb`, `0x16f8cb` (and post-refill acceptance branches `0x16f674`, `0x16f776`, `0x16f879`, `0x16f993`). Retry cap/error and refill visits consequently depend on private coins. No exploit or witness distinguishability is inferred. |
| F2 — same rejection in actual scalar-cell caller | `0x16fd29 mov r12d,[r13+rdi]`; `and`; `cmp`; `0x16fd3d jne 0x16fd50`; rejection back edge `0x16fd42 jne 0x16fc50`. Same source `:424–426`, inline site `:533` | **CHECKED secret-dependent branch.** Distinguishes private candidates P and P−1. The source is unchanged; this is not a wrapper observation. |
| F3 — private-history-dependent mask-block addressing | `0x16f596 lea rdi,[rax*4]`, `0x16f5af mov r13d,[r15+rdi]`; next limb `0x16f696` / `0x16f6af`. Source `state_only_hiding.rs:409–416` | **CHECKED secret-dependent address through rejection history.** The word cursor at `[state+0x50]` increments for rejected words; the next logical limb reads a different offset depending on preceding private candidates. For initial word=0, acceptance of candidate 0 makes limb two read offset 4; rejection of P followed by acceptance makes it read offset 8. Refill occurs at word 8. This is a stateful address dependency, with a corresponding checked branch F1; no claim about cache-line distinguishability or joint privacy. |
| F4 — witness pole decision in caller | `0x94a7c call all_slots_clear`; `0x94a81 mov r12d,eax`; cleanup `0x94970 mov esi,r12d`; `0x94839 test sil,1`; `0x9483d je 0x948a4`; error byte 0xb at `0x948a4`. Source `crates/aspis-r1-cost-probe/src/host_semantic.rs:326–327` | **CHECKED secret-dependent branch.** The verdict depends on witness tuples and lambda/chi. The scan itself is eager; the caller branches on the verdict to return ActivePole. Retained retry/bad-event/coupling obligations are not discharged by the scan audit. |
| F5 — zero boundary in actual M31 inverse | `0x1dfc40 test edi,edi`; `0x1dfc42 je 0x1e049f`. Source `crates/aspis-core/src/field.rs:216` | **CHECKED operand-dependent branch**, secret when operand is secret. Zero takes panic path. Public interpolation/geometry operands are classified separately below; nonzero canonical input removes this particular distinction, conditionally. |
| F6 — zero boundary in actual QM31 inverse | limbs loaded `0x1e0f91–0x1e0f9b`, OR-reduced `0x1e0f9e–0x1e0fa6`; `0x1e0fa8 je 0x1e1457`. Source `field.rs:1007–1008` | **CHECKED secret-dependent branch** at witness-derived inverse callers. Returns None on zero. No nonzero proof is imported from another source cohort or assumed from the function name. |
| F7 — seed zero/short-circuit comparisons, non-proof-account entry | `0x17409d je`, `0x1740b5 je`, `0x1740ce jne`, after fixed-offset OR reductions. Source `crates/aspis-prover/src/state_only_entropy.rs:193` | **CHECKED private-seed-dependent branches** in `generate` (the 96-byte API). Second and third comparisons can be skipped. This binary does **not** retain `generate_for_mask_nonce`; its 64-byte production-route lowering is missing, not inferred from this function. |
| F8 — gamma carry | `0x10054d cmp rsi,0x7ffffffe`; `0x100554 jbe 0x1005fa`. Source `crates/aspis-r1-cost-probe/src/sampler.rs:113–115` | **CHECKED raw-FS-answer-dependent branch**, not classified as a direct witness read. The conditional wrap follows the eight-digit carry. Witness independence of the joint challenge/cost trace remains an obligation. |
| F9 — honest compiler sentinel | `0x1c312d test edi,edi`; `0x1c312f je 0x1c31c4`; `0x1c313e call M31::inv`. Source `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs:213–221` | **CHECKED secret commitment-dependent branch** at the zero sentinel; canonicality guards `0x1c30fc`, `0x1c3105`, `0x1c310e`, `0x1c3119` also inspect commitment limbs. This is constructor/prevalidation-envelope evidence; no claim that both outcomes occur among already-valid prover inputs. |

F1–F9 are static findings in the pinned candidate example, **not a checked
finding against an identified shipped executable**. They forbid an unrestricted
“all kernels/callers are branch/address independent” claim for this artifact.
They do not by themselves refute the privacy theorem: private randomness and
FS answers need the specified joint-trace simulation, and invalid/zero/retry
boundaries need their stated domain and bad-event arguments. No repairs made.

### Reviewed bodies and real call sites

Symbol prefixes in this table: `C=aspis_core`, `R=aspis_r1_cost_probe`,
`P=aspis_prover`, `S=aspis_statement`. Exact unmangled names, extents, instruction
text and resolved incoming sites are in `disassembly/`; no new wrappers exist.

| Kernel/body and interval | Actual call sites / inline carrier | Instruction-level result and limits |
|---|---|---|
| `R::ct_pole::all_slots_clear` `0xcbb50–0xcbca5` | material closure `0x94a7c` | Clean in scan body at fixed valid geometry; Jcc `0xcbb53` tests length, `0xcbb9e` row=1024 bounds, `0xcbc85` public pointer-loop limit. Secret compares `pcmpeqd`, `pxor`, `por`, `movmskps`, `sete`, `and` at `0xcbbf5–0xcbc79`; no pole-position short circuit. Addresses use public row/side/slot counters; V371. Caller F4 remains. |
| `R::host_semantic::copy_tuple_limb` `0x91750–0x917c2` | ten retained calls in endpoint body, `0x95008`, `0x95036`, `0x95064`, `0x95092`, `0x950c0`, `0x950f1`, `0x95122`, `0x95152`, `0x95182`, `0x951b2`; other limbs inline | Descriptor tag/bank/column/row and Vec bounds govern branches. Witness load `0x917a4 [rdx+rcx*4]` uses public registry row rcx; witness+offset reduction `0x917a7–0x917b7` uses `cmovb`, no data Jcc in this arithmetic slice. Clean in this body conditional on public registry geometry; V371. |
| `R::host_semantic::copy_endpoint_values` `0x94b40–0x954ab` | closure `0x946a9`, `0x9475e`; compressor `0x95290` | Reviewed registry-reader and accumulation path: row/side/slot/arity bounds public, trace values enter arithmetic; fixed tuple read/compression and register/SSE selection. No secret-indexed address identified in this valid-geometry path. Error/allocator branches and public shape obligations retained. V371; no blanket whole-closure verdict. |
| `S::logup::compress_tagged_tuple` `0x181bd0–0x1821bf` | endpoint `0x95290`, forest copy rows `0x1d319e` | Clean in body for fixed public tuple length. Only Jcc `0x181beb` on length=0 and `0x1821a5` on four-byte iteration counter. Tuple address uses public byte counter r15. M31 reduction and QM31 multiply inline: ALU/IMUL/SSE/CMOV; no DIV/IDIV. V371. |
| `C::field::M31::inv` `0x1dfc40–0x1e04b9` | interpolation `0xccfd4`; QM31 norm descent `0x1e11b7`; sentinel `0x1c313e`; full incoming list retained | F5. Fixed addition-chain arithmetic on nonzero input has no further Jcc or DIV; fixed stack addresses; IMUL/reduction/select depend on V371. |
| `C::field::QM31::try_inv` `0x1e0f80–0x1e146a` | copy helper `0x182302`, `0x18244b`, `0x1825df`, `0x182769`; circle `0x1dec74`; certificate `0x10b1a1`, `0x132678`; WideExact `0x1e8bf2` | F6; inner CM31 norm is inlined and calls M31 inverse at `0x1e11b7`. Fixed-offset four-limb loads, register/SSE arithmetic and multiplication; V371. Incoming witness/helper and public/challenge operands are not conflated. |
| `S::logup::build_copy_logup_helper` `0x1821c0–0x1829a7` | forest helper `0x18565d`; four inverse sites above | Weight checks before inversion and Option branches after it are visible. Source weight provenance for this route: registry kind, public append index and public variant (`pair_forest_trace.rs::copy_weight`); denominator chi−compressed tuple is witness-derived. Nonzero denominator/NoPole obligation retained. No whole-helper clean finding claimed. |
| `R::host_sumcheck::interpolate` `0xcced0–0xcd230` | actual `M31::inv` call `0xccfd4` | Source denominator is product of i−j for public i,j<28; witness-derived values multiply its inverse afterwards. Inverse branch is therefore public-domain at this caller; its denominator/nonzero source association remains a proof obligation. V371 on witness arithmetic. |
| `R::host_sumcheck::prove_sumcheck_round` `0xcd230–0xcd893` | round driver `0xcd8a0–0xcda4d` | **Variable-latency DIV present** at `0xcd32f div r13`, `0xcd344 div r13d`. Dividend rcx is the evaluation iteration index; divisor r13 is `assignments=1<<(9-round)` from public round; source `host_sumcheck.rs:116–121`. No secret DIV finding here. The 32/64-bit dispatch `0xcd328` uses these public operands. Result/error predicates and other caller bodies not given a whole-function clean verdict. |
| `P::state_only_hiding::SeedExpander::qm31` `0x16f540–0x16f9ea` | sample G `0x16fa88`, H1 padding `0x170156` | F1/F3. `m31` and `next_word` are inlined here; hash function pointer call `0x16f633` (and three later refill copies) has fixed hash target supplied by caller, but private data and secret-history-dependent visit count. No claim that hashing internals were audited. |
| `P::state_only_hiding::sample_mask_cells` `0x16fb80–0x16fe41` | material builder `0x8fbd6`, column sampler `0x170275` | F2 and history-dependent cursor loads `0x16fd29`. Buffer count/accepted output index are public on complete success; that does not make rejection branches public. Error path and cleanup retained. |
| `P::state_only_entropy::StateOnlyAttemptSecrets::generate` `0x173f60–0x174370` | retry owner `0x7e150`, example main `0x604a3` | F7. OS-status branches are distinct from private-byte zero comparisons. `generate_for_mask_nonce` absent: proof-account entropy route not covered. |
| `R::sampler::qm31_sample` `0x1000a0–0x1003f6` | retained callers enumerated in call-sites JSON | Clean in conversion body: no Jcc/DIV/IDIV, fixed input/output offsets; constant-divisor division lowers to multiply/shift/subtract. V371 on raw-block arithmetic. This does not establish joint FS/witness independence. |
| `R::sampler::low_base_p_digits` `0x100650–0x100adb` | gamma `0x100416`; ordinary sampler uses generic inline closure too | Clean in this body: no Jcc/DIV/IDIV, fixed offsets; MUL/shift/subtract constant-divisor lowering depends on V371. Ordinary sampler's separate generic closure at `0xccdd0` is **not** covered by this body's verdict. |
| `R::sampler::gamma_sample` `0x100400–0x100645` | prover semantics `0x7f1cf`; transcript scalar `0x96fb0`; verifier `0xb7cff` | F8; `mul r13` at `0x100452` and further MUL/CMOV/carry operations use block-derived operands; V371. |
| `S::pool_v1::pair_forest_copy_builder::inv_r` inline `0x1d7124–0x1d71c9` inside `CopyRecords::banks` | compiler calls banks at `0x1d1503` | Witness change-digest limb loaded at `0x1d7124`. Exponent r8 initialized to fixed `0x7ffffffd` at `0x1d714c`; Jcc `0x1d7198`, `0x1d719e` depend on public exponent. Remainders use `imul`, magic-constant `mul`, shifts/subtract/add; no DIV or zero guard in this slice. Clean in inverse slice; V371. Enclosing compiler is not thereby clean. |
| `S::pool_v1::pair_tree_profile::…::two_outputs` `0x1c3080–0x1c31da` | compiler `0x1d1339`; fixture witness `0x175976` | F9; source invalid-input/zero-sentinel boundary retained, separately from inverse arithmetic. |
| `C::field::CM31::pow` `0x1e04c0–0x1e069b` | incoming calls retained | Jcc `0x1e04c3`, `0x1e057a`, `0x1e0588` depend on exponent rdx; clean with exponent public/fixed. Secret exponents would make these secret branches. V371 on base arithmetic. |
| `C::field::QM31::pow` `0x1e0770–0x1e0f79` | incoming calls retained | Same qualified finding: exponent tests `0x1e0780`, `0x1e0a6a`, `0x1e0a7f`; fixed input/stack offsets, V371. |
| `C::field::wide_exact::WideExact::pow` `0x1e68b0–0x1e8532` | symbol present; deployed reach not established | Exponent tests `0x1e68cb`, `0x1e741f`, `0x1e7469`; V371. Presence is not a deployed call-graph edge. |
| `C::field::wide_exact::WideExact::try_inv` `0x1e8540–0x1e94f4` | QM31 norm call `0x1e8bf2`; deployed reach not established | Operand-dependent Option guard `0x1e8bfd jne 0x1e94db`, and callee F6. V371; no unrestricted CT verdict. Research inverse inventory excludes a direct deployed-prover call; merely linked support is not counted as witnessed execution. |
| `C::circle::secure_circle_point_from_parameter` `0x1de930–0x1df5d9`, `secure_ood_circle_point_from_parameter` `0x1df5e0–0x1df651` | norm inverse `0x1dec74`; source circle.rs and sampler.rs:121–127 | Raw-parameter-dependent branches: inverse Result at `0x1dec7f`, propagated error `0x1df5fd`, parameter high-half subfield test `0x1df628`. V371 on arithmetic. Challenge/fallback behavior remains joint-trace evidence work; no direct witness input claim. |

### V371 instruction dependence (DOITM OFF)

Pinned CPU in build receipt: Intel Core Ultra 7 155H, family 6, model 170,
stepping 4. DOITM OFF is the D248 owner/host state (no new MSR access or write
in this job). The following observed instructions process private/witness or
raw-answer data and their operand-independent timing is **not** guaranteed by
this audit. The disassembly gives every individual occurrence within the stated
body; these lists identify families, not a new CPU latency proof.

| Body/slice | Instructions requiring V371 for data-operand timing |
|---|---|
| CT pole equality/fold | secret `pcmpeqd`, `pxor`, `por`, `pshufd`, unpack/shuffle instructions, `pslld`, `movmskps`, `cmp`, `sete`, `and`; example secret compares `0xcbbf5`, `0xcbc1e`, `0xcbc3f`, `0xcbc4d` |
| Tuple reader reduction | `lea`/integer add, `cmp`, `cmovb` on witness+offset, `0x917a7–0x917b7`; public address provenance is separately reviewed |
| Tagged compression and inline field kernels | `imul`, `and`, `shr`, `add`, `sub`, `cmp`, `cmovb`, `cmovae`; SIMD `pand`, `pandn`, `psrlq`, `paddq`, `paddd`, `pcmpgtd`, `pcmpeqd`, `pxor`, `shufps`, `orps`, `andps`, unpack; extent `0x181bd0–0x1821bf` |
| M31 addition-chain inverse | `imul`, `and`, `shr`, `add`, `cmp`, `cmovae`, `cmovb`; example first multiply `0x1dfc4d`; nonzero conditional arithmetic extent `0x1dfc48–0x1e049f` |
| QM31 inverse / norm descent | `or`, `add`, `sub`, `imul`, `and`, `shr`, `cmp`, `sbb`, `cmovb`, `cmovae`, `cmove`, plus M31 callee; example norm multiply `0x1e0fc1` |
| Raw FS digit and gamma conversion | `mul` (including `0x100452`, `0x10046d`), shifts including `shrd`, add/sub/OR, carries `sbb`, `cmp`, `cmovae`; ranges in table above |
| Honest compiler inv_r | `imul` `0x1d7170`, `0x1d71a0`; `mul` `0x1d7177`, `0x1d71a7`; shifts/sub/add on witness-derived products |
| Seed comparison/rejection | fixed-offset loads, `or` reductions in generate, `and`/`cmp` in mask sampler, plus secret-data hash calls whose internals were not audited here |

Register selection by CMOV/SETcc and branch elimination are not grounds for
removing V371. Secret memory contents, cache/microarchitectural state and
function-pointer hash/OS/allocator internals are not certified by these tables.
No new trust item is introduced; the capped trust interface is unchanged.

## Coverage, status and next deliverable

**V373: FINDINGS on this supplementary candidate artifact; OPEN for the exact
shipped x86_64 executable.** It is not marked EVIDENCED for deployment.
The shipping entrypoint, exact deployment features/target flags/toolchain and
release artifact binding have not been supplied or found in the pinned branch.
The request for those details remains pending. The diagnostic binary is never
renamed “shipped” and no release/adoption action is performed.

Coverage is explicit: selected extraction is broader than manual review.
The remaining host semantic bodies, complete mask application/balancing path,
sparse-equality weights, QueryScan, multiproof helpers, hash/entropy OS internals,
allocator/stdlib and generic ordinary-sampler closure have **no complete
instruction/provenance audit in this packet**. The 569 incoming sites are an
inventory, not 569 reviewed or proved paths. CodeField/WideExact support
symbols are retained without inventing deployed reachability. The exact
proof-account entrypoint and its generic instantiation are absent in this
example, so adding more example/wrapper builds cannot complete the shipping
requirement. No source-wide or binary-wide absence-of-leakage claim is made.

Stop boundary: checked private-mask branch/address and witness pole-branch
findings F1–F4, reported without fixes, plus the missing shipping identity.
No Lean/Kani runs were useful or needed for this static finding; attempts used
0/30 Lean, 0/0 Kani. No theorem, axiom or formal premise is added or discharged.
No source under crates/programs or any soundness file changed. V373 remains P;
V371 remains substantive; V370 and the L1/L2 domain/coupling/inversion obligations
are retained. Before/after privacy endpoint premises: unchanged. V374 untouched.

Next concrete deliverable: lead pins the deployed proof-account executable's
entrypoint/build recipe (or explicitly selects a release artifact); build it
from this candidate in the same capped workspace, record the new binary identity,
resolve its inline instances and callers, and extend this instruction/provenance
audit to every required kernel/call site. The current findings must be checked
in that artifact, with no assumption that another link preserves their addresses
or lowering. This deliverable is distinct from the later quiet-host V374 run.

Target not yet established.

Evidence consistency validation: `python3 evidence/pv-l3-20261027/validate.py`
passed (1,067 source pins, nine finding/source-line/instruction bindings, binary
identity, symbol/call inventory and two capped receipts). This is an artifact
consistency check, not a CT proof. `git diff --check` passed. Retained binary and
full-disassembly hashes are in `disassembly/retained-binary.json`; binaries are
not committed. Existing pinned host cache is reused and retained.


## Resume stage 1 — approved shipped source, build identity gate

Read snapshot `research` = `73e5a17c35453ed96fc16c692fc1da49133e49fc`.
The release ledger's “Pinned client bundle (owner-approved 2026-10-27)”
identifies source revision `5228877938c7e42a1c87aa35f69f9a110ee9a4d6`,
1,295 files / 12 roots / 16 call-chain steps. The byte-exact pin document is
retained at [shipped/client-pins.json](shipped/client-pins.json), SHA256
`16bd80682bd6b8a489413eed725802d1539e41c1804f8b374cd4b77b0697a7c2`.
This resolves the previous entrypoint question: `devnet_spend::main`, prove
branch, in the standalone `tools/r1-cost-probe` workspace. It does not resolve
the complete build identity. The earlier candidate-example addresses remain
example addresses; none is assigned to this executable.

**Checked build gap, no defaults selected:** the pin document has no toolchain,
feature-selection, flags, target-triple or build-command fields. The pinned
revision contains neither `rust-toolchain.toml` nor `rust-toolchain`.
`tools/r1-cost-probe/Cargo.toml` declares release opt-level=3, and
`scripts/r1_devnet_spend.py:10` defaults to `native-target/release/devnet_spend`;
these are evidence for a release path, not a full invocation.
`tools/r1-cost-probe/src/bin/devnet_spend/plan.rs:77–79` gates actual proving
on `r1p-check`; without it the function returns “build with --features
r1p-check”. That proves a necessary feature, not the complete selected set.
`scripts/r1_devnet_receipt.sh:23` sets
`RUSTFLAGS='-C link-arg=-Wl,--threads=4'` for commands passed through it;
it accepts an arbitrary command and does not select a Rust toolchain or
build features. `scripts/r1_devnet_build.sh` builds the SBF verifier rather
than this native client. No authoritative native build invocation was found
in the pinned scripts/tools/configuration search. Host rustc 1.94.1 from the
example receipt cannot silently become a shipped toolchain pin.

The task expressly says to state missing build fields and not guess. An
as-shipped compilation is therefore pending the lead's exact native build
command, toolchain, selected features and flags. No new host scope, build,
execution, disassembly, timing test, wallet access, Lean or Kani run occurred.
Shipped binary SHA256 / rustc / LLVM / link-time addresses: **not available**.
This is a build-identity blocker, not a new checked side-channel finding.
The source comparison and precise gap are recorded in
[shipped/pin-preflight.json](shipped/pin-preflight.json).

### Lead D268 classification retained

Ledger links below refer to the authoritative research snapshot of
`design/PRIVACY-LEDGER-20261026.md`; that ledger is not modified here.
D268 uses “F6” for gamma carry; this packet's stable IDs retain F6=QM31 inverse
and F8=gamma carry, as in findings.json. No finding is renamed or discarded.

| Existing finding / example address | Class and lead disposition | Ledger row |
|---|---|---|
| F1 `0x16f5bd`, F2 `0x16fd3d`; hiding.rs:425 | secret-dependent branch; rejection of candidate P reveals rejection count, independent of accepted masks/witness in principle; L2 must prove joint simulation | [V354](../../design/PRIVACY-LEDGER-20261026.md), V373 |
| F3 `0x16f6af`; hiding.rs:416 | secret-dependent address through that rejection history; same retained rejection-count argument, no new leak conclusion | V354, V373 |
| F4 `0x9483d`; host_semantic.rs:326 | secret-dependent branch; witness difference only on charged poleBad event | V360 (retry/error prefixes), V373; poleBad containment retained |
| F5 `0x1dfc42`; field.rs:216; F6 `0x1e0fa8`; field.rs:1007 | operand-zero branch; inversion containment D259/D261 remains proof work | V373 / V380-inversion, V371 for arithmetic |
| F7 `0x1740b5`; entropy.rs:193 | private-seed rejection, 2^-256 per seed; example covers generate only | V352 is required for shipped generate_for_mask_nonce; V373 |
| F8 `0x100554`; sampler.rs:114 | raw FS carry branch, lead classifies as public data | V356, V373 |
| F9 `0x1c312f`; pair_tree_profile.rs:214 | commitment-dependent zero sentinel; example-only checked domain boundary | V373 / V380-inversion; V371 |

All addresses in this table belong only to example SHA256 `c7f359d4…`.
The lead's rejection/poleBad assessment is accepted, not re-litigated. It is
not a discharge of V352/V354 or their joint execution obligations.


Pin validation checked every pinned blob at revision `5228877938…`: all 1,295
hashes and sizes match. Comparing to this candidate worktree finds **26 changed
and six missing files**, including field arithmetic, entropy/masks, host semantic
and commitment bodies, Cargo.lock and the planner. These are listed completely
in pin-preflight.json. Consequently the previous candidate host tree cannot be
reused as pinned shipped source without a deliberate source selection. No
hybrid (candidate kernels plus old client planner) is called owner-pinned here.


### Shipped-binary coverage table (pending exact build)

These source anchors use **5228877938**, rather than the changed candidate
line numbers in the example tables. “Pending” is not a clean classification.
Every binary interval and incoming/inline call-site set is unresolved.

| Required family | Pinned source anchors | Binary coverage / ledger obligation |
|---|---|---|
| Complete entry and concrete adapter | tools/r1-cost-probe/src/bin/devnet_spend.rs:13; devnet_spend/plan.rs:80,116; RealR1_client.rs:20,28 | Pending; V373 and complete-client binding; public fixture witnesses do not justify skipping secret-data kernels |
| 64-byte entropy route | prover/state_only_entropy.rs:202 generate_for_mask_nonce | Source inspected: public nonce-zero guard, 64-byte OS draw, two secret seed-zero comparisons with short circuit and retry limit. Machine lowering pending; V352, V373 |
| Mask expander, scalar/QM31 sampling/refills | prover/state_only_hiding.rs:330,350,361,371 per V354 anchors | Pending; V354 and V371/V373; no transfer of candidate addresses |
| Mask application and balancing | same file:169,184 balance_m31/qm31_copy_inactive; :248 apply_h1_padding_mask_for_active; :685 apply_mask_material_for_layout; :771 pair-forest application | Pending; V373/V371. Dependence of geometry, dependent coordinate, error and zero tests must be checked at actual call sites |
| Remaining host semantic bodies | probe/host_semantic.rs:31 point_claims, :45 build_with_helper_mode, :204 extra, :216 build_with_material, :273 no_pole | Pending; V357, V360, V373/V371; include sparse weights, claims, sumcheck, interpolation and tuple/helper inverse containment |
| SHA on seeds, private salts and witness-derived bytes | prover/lib.rs:82 host_hashv, :91 HOST_HASH; selected adapter passes HOST_HASH at plan.rs:116; sha2 dependency/CPU dispatch | Pending: inspect selected software/hardware rounds, dispatch provenance, all callers, fixed schedule, addresses, and variable-latency operands; V354/V359/V360, V371/V373. No hash-internals verdict from wrapper source |
| Poseidon on commitments and trace data | statement/poseidon2.rs; state_only_poseidon.rs; pool_v1/pair_forest_trace.rs and compiler callers | Pending: round schedule, constants/table-index provenance, field lowering and all inline instances; V373/V371. Source filenames do not establish fixed-schedule machine execution |
| FS samplers, circle fallback and query scan | probe/sampler.rs/transcript.rs, core/r0_transcript.rs/circle.rs | Pending; V356/V358, V371/V373 |
| Openings, commitment, sort/dedup and multiproof | probe/prover.rs/host_commitment.rs/multiproof.rs | Pending; V359, V371/V373 |
| Certificate creation, elimination and checking | z4/z9*.rs; c3/build and c3/check | Pending; V360–V364, V371/V373; no runtime proof-generation or elimination run authorized by this static task |
| Signing, errors, allocation, OS/stdlib and indirect edges | devnet_spend main branches and dependency closure | Pending; complete-client execution binding and V373. The pin set is explicitly a conservative source superset, not a reachability proof |

### Resume disposition and next deliverable

V373 remains **OPEN / P**, both before and after this resume. No formal premise
was removed, added, weakened or moved into T. V371 remains the substantive CPU
latency trust item under Secure Boot lockdown; no CPU mode change attempted.
There is no new checked shipped-binary branch/address finding because no exact
shipped binary has been built. No absence-of-leakage claim is made.

The exact native build is blocked by unspecified release fields and the
candidate/pinned-source mismatch. A lead recipe must resolve the intended
source selection without silently combining cohorts; then build and audit
that artifact in the existing owned host workspace under one 6G/8G/swap0/
Tasks64 scope at a time. Record actual feature resolution, rustc -vV/LLVM,
flags/target, binary SHA256, complete extraction and per-call provenance.
No unsupported compiler choice is made simply to spend a compile budget.
Budget retained: 0/30 Lean, 0/0 Kani; no host scope in this resume.

**V374 next deliverable after that audit:** a dudect plan bound to the resulting
shipped binary hash, concrete entry/call sites, fixed public inputs and two
valid witness classes, with rejection/poleBad traces accounted for according
to their L2 obligations; record CPU/DOITM, affinity, sample policy and analysis
before running. The lead schedules the quiet-host window. Timing evidence
will not establish absence of leakage or replace V352–V364 proofs.

Validation: all 1,295 pinned blob hashes/sizes checked against the pinned
revision; candidate comparison retained. Existing packet validator and
`git diff --check` run for consistency, not CT correctness. No build was
launched; target/exit/wall/RSS/swap/axioms receipts for a new build are N/A.
Target not yet established.
