# D272 two-artifact audit: A versus recommended B

**Target not yet established. V373 OPEN/P; V374 OPEN/P.**
B: **recommended recipe pending owner approval; toolchain rustc 1.94.1 unpinned**.
The current B section supersedes the historical no-B-binary status below.
Original failed B is called **B0** here; its unchanged archive and receipt stay
in `dual/B`. No binary is designated shipped. No timing/prover/signing execution
or wallet access was performed in this task.

## B identity and minimal lockfile repair

Candidate source `237e13556180d2ce0320a2760f89b35b5f4f02bb`, plus the
lockfile-only sibling commit `1f02f0ecd7f022670d1a967bd31f33ad8aeb8705`.
All 1,303 archived source inputs match that identity after building.
`B-recommended/source.json` pins each input. This branch already contained the
candidate implementation; no Rust/Lean/manifests were edited.

```diff
 [[package]]
 name = "aspis-r1-cert-build"
 version = "0.0.0"
+dependencies = [
+ "aspis-r1-cert-check",
+]
```

`cargo update --offline --workspace --manifest-path tools/r1-cost-probe/Cargo.toml`
changed only that path-package record, corresponding to the candidate's changed
`docs/research/v8-r0-zk-20261009/c3/build/Cargo.toml` optional dependency.
All **423 registry records are identical**, including version/checksum/source
and dependency lists. Complete diff and comparison are in
[B lock receipt](B-recommended/lock/receipt.json). Lock SHA256:
`08de51ef…a57b3f9` → `8f9334eb…fa6af43`. Commit `1f02f0ecd7` contains this
lockfile alone. The old read-only B0 archive was not repaired in place.

Exact successful recipe (no fallback feature spelling needed):

```sh
RUSTFLAGS='-C link-arg=-Wl,--threads=4' cargo build \
  --manifest-path tools/r1-cost-probe/Cargo.toml --release --offline --locked \
  -j 4 --features r1p-check,aspis-r1-cost-probe/ct-host-prover --bin devnet_spend
```

Host rustc `1.94.1 (e408947bf 2026-03-25)`, commit
`e408947bfd200af42db322daf0fadfe7e26d3bd1`, LLVM 21.1.8,
x86_64-unknown-linux-gnu; cargo 1.94.1. Full `-Vv`, CPU, environment and argv
are in [B receipt](B-recommended/receipt.json). No target-cpu override.
Resolved `ct-host-prover` is enabled for cost-probe/prover/core; private leaf
salts, r1p-check, prover and `insecure-spend-fixture` are present.
C3 build/check select native-kernels/native-workers. `optimized-terminal` and
public-work-trace are absent. See [feature closure](B-recommended/features.json).

| Identity/result | A (historical exact D269 recipe) | B (D272 recommended recipe) |
|---|---|---|
| Source | `5228877938c7e42a1c87aa35f69f9a110ee9a4d6` | `1f02f0ecd7f022670d1a967bd31f33ad8aeb8705` (candidate + lock) |
| Feature difference | r1p-check; CT host off | r1p-check + ct-host-prover; optimized-terminal off |
| SHA256 | `dc31d28c3eb9a793f9e2a8c81e69611b42aa8c2cace1393845cd554d090c357b` | `898005412d46103cfeffe5740f7892ee01d1e3d73a7293338c62e679445b5e67` |
| Size | retained A receipt | 2,729,344 bytes |
| Exit / build wall | 0 / 204.826 s | 0 / 177.478 s |
| Cgroup peak / swap | 2,069,794,816 B / 0 | 1,981,816,832 B / 0 |
| Process peak RSS | A time.log | 646,068 KiB (B time.log) |
| Toolchain | rustc 1.94.1 unpinned | rustc 1.94.1 unpinned; recommended pending owner |

A/B differences combine candidate source and recipe changes; this is not an
isolated causal experiment about the CT feature. A's finding PCs remain bound
to A. No diagnostic example addresses are reused for B.

## A/B findings and N2–N6 honest-domain obligations

[B findings](B-recommended/findings.json) binds each PC to its instruction and
candidate source context/hash. Rows below refer to the authoritative privacy
ledger on research; no ledger or soundness cone is edited. “Expected constant”
is the obligation to prove, **not a proof or measured result**. Prefix guards
must individually have constant outcomes, not merely an identical final error.

| Site / rows | A finding | B finding / machine PCs | Valid-honest guard outcome still to prove |
|---|---|---|---|
| N1, V357/V360/V373/V371 | Limb-prefix JNE at `bd677/bd6a0/bd6a6/bd6ac` despite identical full inequality | CT scan `bf8f0–bfa45`. No limb-prefix Jcc; SIMD loads all four slots. Final verdict at `b5a1d` remains R3 | Full no-pole/retry simulation and CPU instruction latency remain P |
| N2, V354/V360/V373 | Active padding zero and inactive sum guards | `13a08b/13a091/13a097/13a09c`, `13a149` | On active rows all padding limbs zero: three JNE untaken, final JE taken; inactive sum zero: JNE untaken. Public active mask fixes which checks execute |
| N3, V357/V360/V373 | Masked C1 and D/G canonicality guards | Base `b4324/b4332/b4340/b434e`; D/G `b43ba/b4420`; decoder `19aa41/19aa4e/19aa5f/19aa6a` | Canonical masked C1/D/G: all invalid-limb JA and decode-failure JE untaken; fixed shape. Native constructor/reducer association remains P |
| N4, V354/V360/V373 | D/G/H1 sum and aggregate audit branches | Local counts use SETE (`9d835/9d8e5`), sums SIMD; owner `a47a2/a47b1/a47bf/a47cd/a47db` still branches | Balanced 16 C1 and 10 mask-only columns, zero inactive D/G/H1 sums: owner error branches all untaken. Requires compiler/mask balance invariants |
| N5, V357/V360/V373 | Helper sum/Option short circuits | Semantic `b482c/b4836`; owner `a4b85/a4b8f/a4b99/a4ba3/a4bb1` | Whenever reached after nonpole helper success, helper total is Some(0); error Jcc untaken, owner final JE taken. Requires native helperSum/copy balance/padding association |
| N6, V357/V360/V373 | Boundary limb-prefix equality and terminal guard | Boundary `c2bf0/c2bfe/c2c0c/c2c1a`; terminal `c3122` uses full SIMD comparison | Every valid reached sumcheck boundary equality holds (JNE untaken), terminal equality holds (JE taken). Native relation, degree, interpolation and oracle identities remain P |
| N7, V360/V373/V396 | Private signing-key decimal digit/zero branches | Same structure, parser `8bee0–8c14d`; first-digit `8bf0c`, digit-range exit `8bf99`, loop overflow/bounds `8bf9e/8bf86` | **Not constant** over valid decimal byte encodings; private seed bytes have 1–3 digits. Signing observer/storage policy remains P |
| N8, V359/V360/V373 | WrongField early higher-limb scan | Still present before worker launch: `bab92/baba1/babb0/babc5` (full tail in excerpt) | Excluded extension limbs zero for valid base/secure lane messages. Native field-domain association remains P |
| R1, V352/V373/V371 | 64-byte two-seed zero rejection | 96-byte generator `13cc90–13cf5e`: nonce/seed zero predicates `13cdce/13cde7/13ce00` plus OS fill/status paths | Rejection/environment/joint seed law remains P; OS failure witness-independence required by D248 |
| R2/R5, V353/V354/V373 | Seed/D expander rejection and cursor history | `137fd0–13847a`, `13c7e0–13cc89`; rejection/refill retained | D268 count assessment retained; accepted mask independence and complete joint trace law remain P |
| R3/R4, V360/V373/V380-inversion/V371 | Final pole/inverse-zero guards | Pole `b5a1d`; inverse zero `199fd2/19b338` | PoleBad charge does not prove native inverse containment or machine latency |
| R6, V356/V373 | Raw-FS gamma carry branch | `cb544`; QM31/low-digits conversion bodies have no Jcc or DIV | D268 public-FS classification retained, including rejected-prefix law obligation |
| R7, V373/V380-inversion | Commitment canonicality and nonzero sentinel | `17d09c/17d0a5/17d0ae/17d0b9/17d0cf` | Domain boundary retained; compiler association not discharged |

## N1 machine result

The reachable helper closure calls `ct_pole::all_slots_clear` at `b5c5c`.
In `bf8f0–bfa45`, the only three Jcc are `bf8f3` (empty public slice),
`bf93e` (public mask bounds) and `bfa25` (public row-loop end).
`bf95a/bf960/bf967/bf96e` load the four 16-byte slots at fixed row offsets.
SIMD `pcmpeqd` compares every limb, OR combines inequalities and the public
active mask, `movmskps/sete` computes the row bit, and `and al,cl` accumulates
without early exit. The final no-pole bit subsequently branches at `b5a1d`.
Thus **B removes A's observed N1 limb-prefix branches in this scan**, including
when first-limb equality differs while full inequality holds. This does not
remove R3, prove same-public witness privacy, prove the whole call constant,
or discharge V371 for SIMD/compare/select latency. Tuple compression/helper
construction and inverse zero boundaries remain separately classified.

## N7 private fields and static digit-path measurement

The main stdin JSON selects public actions/addresses/fixture note number and
carries public transaction instructions; action=prove constructs its note keys,
salts, input value, membership paths and output witnesses internally from the
fixture selector. It does not deserialize caller-supplied private witness
fields. There is no decimal JSON entropy/mask input on that route.

The separate signing route reads every path in `q["keys"]`, parses its file as
`Vec<u8>` (`devnet_spend.rs:16`), then calls `Keypair::try_from`. A valid 64-byte
keypair encoding consists of private seed bytes **0–31** and public-key bytes
**32–63**; **all 64 bytes** pass through the decimal parser. File names are
strings, not decimal private fields. No key file was opened for this audit.
Pinned dependency source excerpts and hashes are in
[B dependency source](B-recommended/dependency-source.json).

`SeqAccess::next_element_seed 8ddd0–8dfed` calls this integer specialization at
`8df20` for positive tokens (`8dee1` for negative tokens, invalid for a valid
u8 key encoding). `parse_integer 8bee0–8c14d` branches at `8bf0c` on first
ASCII zero; nonzero digits loop through `8bf99` (digit-range terminator),
`8bf9e` (overflow bound, constant for u8) and `8bf86` (cursor/end bound).
`8df96` enforces the u8 range after parsing. The input cursor is incremented
once per consumed digit, so later byte addresses depend on earlier widths.

The following counts are **static branch-path accounting from B's actual
instructions**, not sampled timing, dynamic tracing or executed key parsing.
Assume valid unsigned decimal tokens, no internal whitespace, and a comma or
`]` delimiter in the buffer. Counts exclude SeqAccess, I/O, allocation and
Keypair validation. The checked PC sequences are in
[N7 paths](B-recommended/N7-static-paths.json).

| Byte encoding | Digit-range loop tests | Additional digit-consumption iterations | Jcc executions inside parse_integer |
|---|---:|---:|---:|
| `0` | special leading-zero path | 0 | 7 |
| `1`–`9` | 1 | 0 | 10 |
| `10`–`99` | 2 | 1 | 13 |
| `100`–`255` | 3 | 2 | 16 |

For nonzero d-digit bytes the count is `3*d+7`: four entry/first-digit tests,
`d` digit-range tests, two checks for each of `d-1` further digits, and five
post-digit/sign tests. The width-dependent branch pattern persists for valid
byte arrays. A valid full keypair imposes additional public-key consistency;
this audit does not demonstrate a same-public valid key pair, exploit,
distinguishing advantage or witness leak. V396 must explicitly account for
key loading/storage in the full observer.

## Reachable kernel coverage in B

`main 9b280` → `plan::run 7c140` → `plan::prove 84650` →
`prove_masked_retrying a4e70` → `retry_attempt 9dcb0` →
`StateOnlyAttemptSecrets::generate 13cc90` and `prove_masked_attempt a4030` →
`build_with_material b3680` → helper closure `b5550` → CT pole scan `bf8f0`.
Source associations supply inlined adapters/function pointers; actual resolved
call sites and relocations are retained. B's binary contains no symbol for
`generate_for_mask_nonce`; that 64-byte API is not on B's actual entry route.
Its absence is an adoption/client-binding difference, not evidence for that
route. A later proof-account-bound B would be a new build/audit target.

`B-recommended/inventory.json` retains 751 selected symbols; the resolved
symbol closure has 1,413 symbols, 686 selected. This is a lower bound, not a
verified complete transitive taint graph. `kernel-review.json` and
`extra-kernels.json` retain branch/DIV/indirect inventories per named body.
The table describes reviewed source/machine slices and their input provenance.
“Fixed/public schedule” always retains CPU latency V371 and the stated domain;
it never means absence of leakage.

| B family/body | Branch/address and operand classification | Ledger rows |
|---|---|---|
| Entry/planner/retry above | Public action/shape/variant/fixture selector dispatch; result/error/retry history observable. 96-byte entropy has three zero guards and OS status/partial-fill/error paths. Failure witness-independence not proved | V352/V360/V373/V396/V371 |
| Seed construction `b0bc0–b130e`, reservation `b1310–b1877`, derive seed `13a4e0–13a591` | Public layout/nonce/binding/durable store controls shape; private entropy zero guard remains; private seed enters SHA; all error/lifetime prefixes require the joint law | V352/V354/V360/V373/V371 |
| Expanders `137fd0–13847a`, `13c7e0–13cc89` | Rejection Jcc at `13804d/13814d/13824b/13835b`, `13c85d` and analogous subsequent limbs; private sample cursor/rejection history chooses refill/load. Refill HashFn is HOST_HASH from planner | V353/V354/V373/V371 |
| D derivation `13d790–13e364`, salts `13d520–13d783` | Public dependent coordinate/layout/index/tree/attempt grammar; private D arithmetic and leaf seed SHA operands. Rejection and inverse/nonzero domains remain independent of fixed loops | V353/V359/V360/V373/V371 |
| Apply `1393e0–13a044`, wrapper `13a2b0–13a44b`; balance `139060–1392f2`, QM31 `139300–1393d5` | Public generated cells, active flags and dependent coordinates select addresses. Secret values feed fixed scalar/SIMD/cmov arithmetic in reviewed loops. N2 and N4 override any enclosing schedule description | V354/V360/V373/V371 |
| Semantic owner `b3680–b554b`, closure `b5550–b5d1e`, copy endpoint `b5d20–b668b`, helper `1464b0–146c97` | N1/N3/N5. Public registry selects tuple bank/row/limb/slot and copy weights; private tuple data enters compression and witness/challenge inverse denominators. Public shape/error guards need caller validity; no whole-owner CT verdict | V357/V360/V373/V380-inversion/V371 |
| Point claims `b20c0–b2447`, extra `b6690–b6c24`, oracle `b04f0–b0bbc`; sumcheck `c29e0–c3043`, rounds `c3050–c31fd` | Fixed public lane/row/sample/assignment loops; private field interpolation/terminal operands. N6 remains. CT recipe adds fixed worker partition and public assignment-index DIV, not a secret-indexed table | V357/V360/V373/V371 |
| Terminal/selected mask `19be10–19ee2d`; sparse equality `1740f0–174b0a` | Point-derived coefficient selection/pruning depends on raw FS point and public Boolean suffixes; private witness values are arithmetic operands. Joint rejected-prefix challenge/address law required. Generic inline terminal instances lack exhaustive instruction-to-source taint proof | V357/V373/V371 |
| Commitment `ba7d0–bb690`, encode lane `be120–bf835`, encode evaluators `bbee0–bd724`, leaf bytes `bdb80–be119` | Public lanes/lengths/recursion geometry; N8 zero-tail guards retained before fixed worker partitions. Private masks/witness/salts enter codeword arithmetic and SHA. Opening word/salt positions and multiproofs depend on FS queries/history | V359/V360/V373/V371 |
| Query scanner in `Transcript::queries b7c40–b8a2a` | Ordered raw-FS candidate/duplicate/history control and accepted-list addresses. Source scan is inlined here; A's standalone QueryScan PCs do not transfer. Accepted public list alone does not establish rejected-prefix simulation | V358/V373/V371 |
| Public samplers `cb090–cb3e6`, low digits `cb640–cbacb`, gamma `cb3f0–cb635` | QM31/low-digits have no Jcc/DIV; fixed-offset multiply/shift lowering. Gamma `cb544` depends on raw FS carry, retaining D268 public-data classification | V356/V373/V371 |
| P_R1 `cbe00–cc3fe`, C3 build/check inventory | Public-check source inputs are public challenges/C1 root. Pivots/zero skips/swaps/rank/error/panic and worker completion depend on that transcript/certificate; not a direct raw witness read, but joint law remains P | V360–V364/V373/V371 |
| Field inverse `199fd0–19a849`, QM31 `19b310–19b7fa` | Zero guards remain. Fixed nonzero exponent chains use IMUL/add/shift/cmov/SIMD. Interpolation denominators use public sample indices; helper inverse containment requires nonpole and source association | V373/V380-inversion/V371 |
| Compiler `CopyRecords::banks 18f6b0–1917bd`, leaf `two_outputs 17d020–17d17a` | Compiler fixture/public shapes control layout. Private keys/salts/value feed Poseidon and fixed field paths; canonical commitment/nonzero sentinel R7 remains. Full compiler-to-relation validity remains P | V370/V373/V380-inversion/V371 |
| Secret erasure/drop and host worker callbacks | Fixed public buffer lengths control stores; retry/error status changes buffer existence and callback completion. Source workers partition public ranges and preserve ordered result/error selection; OS scheduling/error timing is not proved | V352–V354/V359/V360/V373/V371 |
| Simulator Coins | Real main/prove route does not call sim_e/Coins. Symbol inventory is not a simulator run | V355 |

## Hash and signing internals in B

`HOST_HASH` resolves to `aspis_prover::host_hashv 13c070–13c3cf`.
Private seed derivation, seed-expander refills, leaf-salt derivation and encoded
private commitment messages reach SHA compression. Private note nullifier keys,
salts and values also reach Poseidon. Data is not classified public merely
because it eventually contributes to a commitment.

| Reviewed B body | Schedule/address finding | Rows |
|---|---|---|
| SHA-256 wrapper `13c070–13c3cf` | Segment count/length, buffer remainder and public padding positions select branches. Private content is state input; fixed caller grammar fixes lengths. Rejection history changes refill invocation count | V354/V359/V360/V373/V371 |
| SHA-256 software/dispatch `1babb0–1bd7d2` | CPU state selects dispatch (`1babd5/1babe3/1bd7ab`); block count/end select software loop (`1bac20/1bd73d`). Fixed block offsets, state stack slots and RIP-relative constants; no secret-state round-table index or DIV observed in this body | V373/V371 |
| SHA-NI `1bd830–1bdbec` | Exactly two Jcc, `1bd85a/1bdbc0`, on block count/end. Fixed message/constant addresses, fixed SHA round instruction sequence | V373/V371 |
| Poseidon round `17ddf0–17f954`, sponge `17f960–183014`, node `184020–186662`, trace pair `186670–18708f` | Round/lane class/index and input arity drive control/constant addresses; private state feeds field operations. Node loop bounds are fixed 4 full/18 partial/4 full rounds. No secret-state lookup observed in reviewed bodies | V357/V373/V371 |
| SHA-512 software `1bdce0–1c181b`, AVX2 `1c1820–1c23b3`; secret expansion `1b2ab0–1b2c09` | Secret expansion has no Jcc; compression loops use block count/end and fixed round counters/constants. CPU dispatch public. Signing buffer grammar has fixed secret-prefix length and public message length | V373/V396/V371 |
| Ed25519 basepoint `1b5930–1b5f64`, select `1b6690–1b696b`, conditional assignment `1ba6b0–1ba7a8` | Basepoint caller passes public w=4 (`1b5959`). Select body has no Jcc, loads all eight fixed table offsets and conditionally assigns using SETcc/arithmetic. Private digit does not select table address in this body | V373/V396/V371 |

These are named-body schedule/address findings, not ROM, freshness/collision,
CPU-latency, whole-signing or whole-client proofs. Historical DOITM OFF evidence
is reused; no CPU mode or runtime dispatch was forced during this static audit.

### DIV/IDIV review

All 21 selected DIV occurrences and operands are retained in
[B division inventory](B-recommended/division.json); no selected IDIV was found.
B introduces DIV in the public worker/sample partition relative to A's recipe.

| B DIV PCs / family | Operand provenance |
|---|---|
| `c1e2b/c1e45`, host_work map callback | Public global sample/assignment index and assignments per sample, used to reconstruct sample/Boolean point; private oracle values follow this indexing |
| `c2adf/c2af4`, sumcheck merge | Public evaluation index divided by assignments per sample; result chooses one of 28 sample accumulators |
| `120412/120667` eqw; `121197/1212cc` pfac; `121ea3/121eb2` bterm; six pcoef PCs; `124142/12414f` rr_ent | Public descriptor, degree, row/index and power-table dimension arithmetic; coefficients multiply field values after these combinatorial indices |
| `132d64`, nvec_ok | Certificate pivot index modulo public matrix width; certificate/challenge joint law retained |
| `1b7f11/1b7f27`, Scalar::as_radix_2w | Generic public window-width metadata division; main basepoint caller passes w=4 and takes specialized no-DIV path |

No listed DIV has a raw private limb as its identified operand. This provenance
review does not prove variable-latency execution independent of all secrets or
exclude DIV in unreviewed dependency/OS paths.

## Fixture feature and reachability

The manifest's `aspis-prover/insecure-spend-fixture` feature is unchanged and
confirmed enabled. It makes these APIs available to compiled Rust callers:
`StateOnlyAttemptSecrets::deterministic_spend_fixture`, the v7 transfer/withdrawal
nullifier/prepare/mined/unmined fixture functions, `r0_fixture::{prepare,
statement_public, Fixture::public, Fixture::prove}`, and the forced-selector
`build_hiding_atomic_state_only_spend_proof_v3`. Cost-probe also exposes its own
`prove/prove_masked_fixture` route. **None is linked as a named executable
symbol or targeted by a resolved call edge in B**, and the reviewed main source
route contains no call or callback into them. The source call chain above,
HOST_HASH callback provenance and linked call/relocation inventory together
confirm none of those fixture APIs is reachable from this main. `cfg(test)`
injection/test_hooks are not enabled. See
[fixture review](B-recommended/fixture-review.json).

This does not make the devnet tool an arbitrary-witness wallet: its own
`plan::note` and `plan::digest` deterministic fixture construction **is reachable**
(`84440–8464f` for note). Feature availability, linked API presence and reachable
local fixture construction are separate facts. No manifest/source change was
made to remove fixture facilities or alter that behavior.

## Status, validation and handoff

B's locked-build blocker is repaired and the recommended binary is available.
N1's observed scan prefix branches are removed in B. N7 persists; N2–N6 and N8
have explicit constant-valid-domain obligations, not new assumptions or proofs.
V373 remains OPEN/P: the named families and actual instructions above are
reviewed, but exhaustive transitive taint classification of every inline
specialization, allocator/stdlib/error path, callback and dynamic libc/OS path
is not complete. The selected-symbol direct closure is a lower bound.
No absence-of-leakage conclusion follows from the CT feature, this audit or
a future dudect non-detection.

The [current V374 plan](V374-PLAN.md) binds to B's exact source/features/recipe
and SHA, specifies diagnostic versus honest classes, initial/max sample counts,
90-minute kernel-family windows and a separate four-hour attempt window for
the lead to schedule. It remains proposed; no timing sample was taken. A new
harness must pin its own executable and demonstrate kernel instruction identity;
B's fixture interface cannot inject arbitrary same-public witness classes.

Before/after `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` and its
deployment premises are unchanged. **No formal premise removed, added, weakened
or moved into T.** V352–V364 joint law/native association, V370 preservation,
V371 latency, V373 closure and V396 client binding remain. Trust T retains
exactly entropy_law, entropy_kernel and observation. 0/30 Lean (not needed for
the requested native audit); 0/0 Kani. No prohibited proof shortcut or source
change. No keys/accounts generated, accessed or deleted.

Five sequential scopes cover offline lock update, optimized build, extraction/
metadata/source validation, PC/kernel/parser review, then supplemental review/
identity validation and target-only cleanup. Every scope uses 6G/8G/swap0/
Tasks64, admission barrier and quiet-window shim; no refusal or bypass.
Receipts record target/revision/exit/wall/cgroup peak/swap, with GNU-time peak
RSS and swaps in paired logs and `resource-summary.json`; #print axioms is N/A
for native work. `closure-receipt.json` binds all 1,303 inputs, the single-file
candidate delta, all registry records and reviewed instruction PCs to B's
retained binary/full disassembly hash. `cleanup.json` confirms task Cargo
targets removed; the retained executable is outside git. No executable,
archive, .olean, Cargo target or key is committed.

Next concrete deliverables: lead/owner pins adoption recipe/toolchain/client
binding, schedules V374 with valid class construction and reviews N2–N6 native
invariants; complete remaining transitive V373 and V371 obligations. **Target
not yet established.** Historical evidence follows unchanged in meaning.

---

# Historical D269 audit: A and original failed B (B0)

Status: in progress. Target not yet established. No binary is designated the shipped binary.

A: pinned client source `5228877938c7e42a1c87aa35f69f9a110ee9a4d6`.
B: read-only candidate `237e13556180d2ce0320a2760f89b35b5f4f02bb`.
Both use the D269 devnet R1 recipe, toolchain unpinned (host default rustc recorded per receipt).
The archive source pins retain the entire selected source roots, including the standalone workspace lockfile.
No wallet, prover execution or timing measurement is part of this build/audit.

The B planner directly calls `prove_masked_retrying`; A calls
`RealR1_client::prove_for_proof_accounts`. The 64-byte entropy route must not
be invented for B. Absence from B's actual call chain is an adoption/client
binding difference, not a clean verdict for that route.

The exact requested recipe enables `r1p-check`, which does **not** imply
`ct-host-prover` or `optimized-terminal` in either artifact. In B, the rewritten
field leaves and CT pole scan are behind `ct-host-prover`; this build therefore
does not select them. The previous diagnostic build did select them. An audit
of this requested B artifact cannot be relabelled evidence for a future build
with those extra features. No feature is silently added to the recipe.

Both sequential builds reuse one task-owned Cargo cache (`dual-target-A`);
source archives are separate and are never edited. Cargo validates separate
path-dependency fingerprints. All target directories will be removed at finish.

## Build result and checked B blocker

Both results: **devnet R1 recipe, toolchain unpinned (host default rustc 1.94.1)**,
LLVM 21.1.8, cargo 1.94.1, x86_64-unknown-linux-gnu, no target-cpu override.
`RUSTFLAGS=-C link-arg=-Wl,--threads=4`; other Cargo/Rust environment and exact
argv/cwd are retained in each receipt. A and B are never called the shipped binary.

| Artifact | Result | Wall | Cgroup peak | Swap | Binary SHA256 |
|---|---|---:|---:|---:|---|
| A, 5228877938 | exit 0 | 204.826 s | 2,069,794,816 B | 0 | `dc31d28c3eb9a793f9e2a8c81e69611b42aa8c2cace1393845cd554d090c357b` |
| B, 237e135561 | exit 101, before compilation | 0.190 s | 58,355,712 B | 0 | unavailable: no B executable produced |

B's exact Cargo error: “cannot update the lock file …/dual-B/tools/r1-cost-probe/Cargo.lock
because --locked was passed to prevent this”. See `B/stderr.log` and `B/receipt.json`.
The standalone lockfile is unchanged between A and B. Its `aspis-r1-cert-build`
package has no dependency list; B's `c3/build/Cargo.toml:17–21` adds optional
`aspis-r1-cert-check`, selected through z4's new `native-workers` features.
This is a concrete stale-lock dependency-edge mismatch, rather than a missing
registry download or a memory failure. No lock regeneration, removal of
`--locked`, feature change, candidate edit or unchanged retry was performed.
The root Cargo.lock change does not repair a standalone workspace's lock.

This prevents the requested two-binary audit and B address comparisons. Every
B address in the findings/coverage is explicitly unavailable. A source analogy,
a root-workspace/example artifact or A's retained binary cannot fill that cell.
Lead/owner action: obtain a corrected candidate revision with its standalone
lockfile updated under the release process, then rebuild B with the same recipe
and approve/pin the actual adoption features and proof-account route. The
current B archive stays read-only. No new Lean proof can make this command
succeed without changing its inputs; 0/30 Lean, 0/0 Kani are used.

## Checked new pole comparison finding (N1)

A's `host_semantic.rs:292` (`clear &= chi != *value`) is inlined in
`build_with_material::{{closure}}`, `0xbcd90–0xbd876`. The final verdict is
at `0xbd6cf`; its D268 poleBad classification is unchanged. But **individual
limb equality is implemented by earlier secret-dependent branches**:

```text
bd69d: cmp r10d,DWORD PTR [r8]
bd6a0: jne bd660
bd6a2: cmp r11d,DWORD PTR [r8+0x4]
bd6a6: jne bd660
bd6a8: cmp ebx,DWORD PTR [r8+0x8]
bd6ac: jne bd660
bd6ae: cmp r15d,DWORD PTR [r8+0xc]
bd6b2: setne r9b
```

`r10d/r11d/ebx/r15d` are chi limbs loaded from the closure's challenge
arguments. `r8` traverses compressed private witness slot values. The branch
`0xbd677` is the paired-slot first-limb comparison in the same loop. Row-mask,
row index and slot iteration branches are public geometry. The accumulating
`clear` flag is not the only observable control here: the comparison itself
short circuits. No `ct_pole::all_slots_clear` is selected by this recipe.

For a single slot, chi=(7,11,13,17), value=(8,11,13,17) takes `bd6a0`; whereas
value=(7,12,13,17) reaches `bd6a6`. Both full QM31 comparisons are unequal,
so the final no-pole bit for that slot is identical. This is a checked machine
predicate/path counterexample to classifying **all** these branches solely by
full-field pole equality. It is not a constructed same-public honest witness
pair or an attack-probability result. No claim is made about attainability of
these particular slot tuples in the complete relation. The source-to-observer
joint simulation/containment obligation remains [V357/V360/V373](../../../design/PRIVACY-LEDGER-20261026.md).
B address: **unavailable**, locked build failed; no example address is substituted.
No fix was made. The D268 rejection and final-verdict assessments stand.

Reach chain in A: `devnet_spend::main 0x8c000` → plan prove
`0x795f0` → `0x7ccfc` calls retry owner `0x8db60` → `0x8dbf5` calls
64-byte `generate_for_mask_nonce 0x118280` → `0x8dc92` calls attempt
`0x99060` → `0x99c43` calls `build_with_material 0xbac50` → `0xbba7e`
calls this closure. The adapter is inlined in the planner/owner instance;
`RealR1_client.rs:20–28` supplies the source association.

## Other checked sites

`findings.json` binds every listed PC to its exact extracted instruction and
source revision/context. IDs R1–R7 retain rejection, final pole, inversion,
gamma-public and commitment-domain findings. N1–N8 are additional checked
sites; every B cell is unavailable rather than a copied address.

| New ID | A PCs (examples; all retained in JSON) | Source at A | Class / implication | Rows |
|---|---|---|---|---|
| N1 | `bd677`, `bd6a0`, `bd6a6`, `bd6ac` | host_semantic.rs:292 | secret-dependent limb-prefix branches on compressed witness slots; separate from final poleBad | V357/V360/V373 |
| N2 | `115bab`, `115bb1`, `115bb7`, `115bbc`, `115c71` | state_only_hiding.rs:259–266 | secret-material zero/sum guard branches; active-zero and balancing invariants need caller containment | V354/V360/V373 |
| N3 | `bb1ca`, `bb1d8`, `bb1e2`, `bb1ec`, `bb202`, `bb254` | host_semantic.rs:60–68 | secret-derived canonical-column guards; constant for canonical valid construction only after association proof | V357/V360/V373 |
| N4 | `99843`…`99944` | prover.rs:139–154 | private D/G/padding sum equalities and mask audit branch; intended balances are proof obligations | V354/V360/V373 |
| N5 | `bbb12`, `bbb1c`, `99ce3`…`99d0f` | host_semantic.rs:99; prover.rs:160–161 | helper total equality/Option short circuits; helperSum/native association retained | V357/V360/V373 |
| N6 | `9fc4b`, `9fc5b`, `9fc6b`, `9fc7b`, `a0137` | host_sumcheck.rs:64,75 | witness-derived boundary and terminal equality branches; honest validity does not follow from compilation | V357/V360/V373 |
| N7 | `835ad`, `835bc`, `8363c`, `83649` | devnet_spend.rs:16; serde_json 1.0.151 de.rs:462–507 | private key decimal JSON parsing: first-digit/digit-count branches, subsequent positions depend on secret byte widths | V360/V373/V396 |

N2–N6 expose predicates of private-derived operands but are expected to be
constant when the relevant native invariants hold. Their presence is checked;
an actual differing honest trace is **not** proved. They are not silently
placed in poleBad or the rejection count argument. N7 is on main's signing
branch, separate from action=prove: secret key JSON decimal representation has
variable digit counts. `SeqAccess::next_element_seed` calls the integer parser
at `0x854a1`/`0x854e0`; key conversion is reached at `0x85af8`. No actual key
file was opened. This reports a key-loading observable, not a proved witness
privacy attack. Full signing/storage observer policy is still V396.

## A coverage and instruction/provenance classification

All A intervals refer to **devnet R1 recipe, toolchain unpinned (host default
rustc 1.94.1)**, SHA `dc31d28c…090c357b`. Every B interval is unavailable.
The selected assembly retains 640 symbols; the resolved-symbol direct call/tail
closure from main has 1,143 symbols, 578 selected. It is a lower bound because
register callbacks, externs and inlining need manual provenance. The first
extraction mistakenly counted intra-function jump destinations as symbol nodes;
`extraction-initial.json` retains that run, and `extraction.json` corrects the
count, with signing/parser extraction added. Full assembly bytes are unchanged.
These counts are inventory, not reviewed-kernel or theorem counts.

“Clean in body” below means the reviewed body has fixed/public schedule and
addresses for the stated inputs; it is not an absence-of-leakage claim. It always
retains V371 for secret-dependent instruction operands. N/R findings override
any enclosing generic arithmetic description. Rows link to the authoritative
[privacy ledger](../../../design/PRIVACY-LEDGER-20261026.md), read from research;
that ledger is not edited.

| Family / A body | Review and operand/address provenance | Classification | Rows |
|---|---|---|---|
| Entry / planner `0x8c000`; prove `0x795f0–0x7f75b`; retry owner `0x8db60–0x8dd9e` | Public JSON selects action, variant, note fixture, live state, retained public proof-account list. Source A adapter is inlined; 64-byte generator edge checked above. Retry count selects callback/public nonce and eventual account, requiring joint law. Signing branch separately contains N7. | R1/R3 and public-dispatch branches; unresolved whole-client policy | V352/V360/V373/V396 |
| Entropy `0x118280–0x11850e` | Public nonce guard, OS function dispatch/partial fill/status/interrupt branches; two private 32-byte zero predicates and bounded retry; fixed-offset erasure. No OS kernel/provider timing proof. | R1 secret-dependent branch; relies on V371; OS-failure independence P | V352/V373/V371 |
| Seed expansion `m31 0x114a60–0x114b9b`, `qm31 0x114ba0–0x114fe7` | Refill hash target is HOST_HASH from planner; cursor reflects rejection history. Four rejection branches in qm31 at `114c96/114d88/114e7b/114f75`. Retry-limit/result propagation retained. | R2 secret-dependent branch/address | V354/V373/V371 |
| D expansion `0x117e40–0x118276`, `derive_pool_v1_zero_factor_d 0x118e80–0x1198bf` | Same four-limb pattern for private D seed; layout flags/first inactive coordinate derived from public generated masks; sum scans use public row/dependent indices. | R5 secret-dependent branch/address; balancing arithmetic relies on V371 | V353/V373/V371 |
| Material construction `0xb94b0–0xba06f`; reserve `0xba070–0xba9e4`; private-entropy seed guard `0x116000–0x1160b1` | Nonce/context comparison and durable storage use public context in A; source `derive...:390` guards private entropy zero (`0x116028`, same zero-domain rejection concern as R1). Seed is hashed at `0x11608e`. Counts/layouts come from generated relation-free cells. | secret-dependent zero guard/rejection; public geometry; V371 | V352/V354/V360/V373 |
| Apply mask material `0x115220–0x115b66` | Shape and public cell `(column,row)`/active flags choose loads and dependent coordinates; mask/witness contents enter field add, not cell selection. The generated-cell provenance is source-based; no formal complete descriptor association claimed. | clean arithmetic/address slice under public geometry; V371; error/allocator prefixes P | V354/V360/V373/V371 |
| Balance M31 `0x115070–0x115133`, QM31 `0x115140–0x11521d`, first inactive `0x114ff0–0x11506d` | Branches use table length, row/dependent and active flags; secret sum lowers to `cmovb`/SSE masks. Dependent store is at a public generated coordinate (`115114`, `1151fc`). No DIV/IDIV in these bodies. | clean in these bodies for public geometry; relies on V371 | V354/V373/V371 |
| H1 padding `0x115b70–0x115cb6`; wrapper `0x115f70–0x115ffe` | Public active scan, secret-value/inactive sum guards N2, then fixed 1,024-cell add loop `115c80–115cb1`. | N2 secret-dependent branch; addition slice clean + V371 | V354/V360/V373/V371 |
| Native mask audits in attempt `0x99060–0x99fd0`; `inactive_sum_k 0x95040…` | Public row mask gates loads. Private-derived sum predicates short circuit; counts and final owner error retained. | N4/N5 secret-dependent branch; V371 arithmetic | V354/V360/V373/V371 |
| Host semantic owner `0xbac50–0xbcd8a` | Public statement/shape comparisons, masked C1/D/G canonicality N3, C1 commitment before lambda/chi, helper/no_pole closure, H1 sum N5, semantic transcript, claims, OOD endpoints. Error/Result/Option paths retain caller conditions. | N1/N3/N5; no whole-owner clean verdict | V357/V360/V373/V371 |
| Tuple readers/compression in helper closure `0xbcd90–0xbd876`; `compress_tagged_tuple` retained in inventory | Registry descriptor supplies bank/column/row and slot index; private field value enters reductions/compression. Bounds and arity checks depend on descriptors. Private chi/slot partial equality N1 precedes final pole verdict R3. | N1/R3; arithmetic/address slices under public registry rely on V371 | V357/V360/V373/V371 |
| Copy helper `0x135ea0–0x135f7b` → `build_copy_logup_helper 0x11bbc0–0x11c307` | Weight-zero guards at `11bca5/11be0d/11bf62/11c0c8`; source copy weights depend on public append index/transfer variant/static registry. Secret tuple values enter denominators and QM31 inverses, with Option-error guards at `11bcfa/11be56/11bfb8/11c111`. | public-weight branching; inverse/pole containment retained R3/R4; V371 | V357/V360/V373/V380-inversion |
| Point claims `0xba9f0–0xbac45`; MLE `0x163ba0–0x163c26`; extra `0xbda40–0xbdff8`; oracle closure `0x9ee40–0x9f665` | Loop counts/column indices fixed 29/10/28, public points/variant; private column values feed fixed field interpolation/Horner arithmetic. Terminal constraints and errors called through the closure; no inferred whole-terminal clean verdict from wrapper. | clean reviewed fixed-loop slices; V371; native terminal closure proof P | V357/V373/V371 |
| Sumcheck `0x9fa80–0xa01d3`; interpolation `0x9f670–0x9fa80` | Public round/sample/Boolean assignment loops; no DIV/IDIV in this non-CT recipe. Interpolation denominator uses public i,j in 0..28; witness values only multiply its inverse. Boundary/terminal predicates N6 remain. | N6; public inverse denominator; V371 arithmetic | V357/V360/V373/V371 |
| Sparse equality `0x163210–0x163b99`; state-only selected mask `0x1789a0–0x17b847`; extension Poseidon terminal symbols retained | Suffix pruning/selected coefficient addresses use point coordinates derived from raw FS challenges and public Boolean sumcheck suffixes, not opened private field contents. Hidden rejected prefixes still require joint simulation. Full terminal instruction-to-source provenance for all inline specializations remains incomplete. | challenge-dependent branch/address, L2 obligation; V371 | V357/V373/V371 |
| QM31 sampler `0xa15a0–0xa18f6`; low digits `0xa1c50–0xa20db`; gamma `0xa1900–0xa1c4e` | First two bodies have no Jcc/DIV/IDIV, fixed offsets and constant-divisor multiply/shift lowering. Gamma R6 branch at `a1a59` on raw FS carry. | clean conversion bodies + V371; gamma public-data branch under D268 | V356/V373/V371 |
| QueryScan `0x176530–0x176651`, pairs `0x176370–0x176529` | Candidate/duplicate/history control depends on FS query stream; accepted public query list alone does not prove rejected-prefix simulation. | challenge-dependent branch/address; L2 retained | V358/V373/V371 |
| Encoder/commitments, backend `0x942f0–0x94cea`; host_commitment symbols retained | Public lane/time/length/recursion geometry; witness/masks and private salts enter encoded values and SHA inputs. Non-CT WrongField guards test higher secret-derived limbs (same canonical-domain concern as N3). Query-indexed word/salt addresses and sort/dedup/multiproof structure depend on published query data/history; need full joint law. | secret-derived validation branches; challenge-dependent addresses; V371 | V359/V360/V373/V371 |
| P_R1 `0xbf310–0xbf90e`; public data `0xbf910–0xc0b88`; builders `0xc0b90–0xc3565`; z9c/z9d, C3 build/check bodies retained | Public-check owner receives public challenges and C1 root, not raw witness/mask arrays. Pivot searches, zero skips, swaps, rank tests, matrix dimensions, allocator growth, caught panics and errors depend on that transcript/certificate. This source dataflow does not discharge joint rejected-prefix simulation. | challenge/certificate-dependent branches/addresses; public-metadata DIV sites below; V371 arithmetic | V360–V364/V373/V371 |
| Field inverse `M31 0x171740–0x171f45`, QM31 `0x172990–0x172e68`; inline field reducers in compression/encoder/hash/terminal | Zero guards R4; nonzero exponent chains fixed; arithmetic uses IMUL/add/shift/cmov and SIMD masks. Old CT-feature example addresses do not apply. Other pow/CodeField monomorphizations in inventory require their caller's public-exponent/nonzero facts. | R4; relies on V371; inverse boundary P | V373/V380-inversion/V371 |
| Compiler `CopyRecords::banks 0x126e10–0x128f1d`; extracted path writer `0x170f40–0x170fd7`; leaf `two_outputs 0x163cc0–0x163e1a` | inv_r exponent constant P-2, constant-modulus lowering uses multiply/shift. Path block writer fixed row loop; private contents do not select path-row layout. Leaf commitment canonicality/nonzero sentinel R7 retained. Full compiler checks/source-to-relation domain not discharged by these slices. | fixed arithmetic slices + V371; domain branches R7 | V373/V380-inversion/V371 |
| Erasure/drop of secrets/material/salts | Fixed buffer lengths and public collection shapes control stores; sample exhaustion/retry changes which buffers exist. Drop does not make prior traces constant. | clean erasure slices under length provenance; rejection/error lifetime P | V352–V354/V359/V360/V373 |
| Simulator Coins | Real `devnet_spend` action=prove does not call `sim::sim_e`/Coins; symbol inventory is not a simulator run. | not reached by selected real route; no V355 discharge | V355 |

For the encoder WrongField predicates, A source `host_commitment.rs:170–175`
tests extension limbs of witness-derived messages before choosing base versus
secure lanes. This is N8, an additional member of the canonical/field-domain validation
family, not a claim that valid messages fail. Its early-zero scan PCs are
`0xb2c64` and `0xb2c9a`, with the source/PC association retained in findings.json.

**Completeness limit:** these are reviewed named bodies and source/provenance
slices, not a verified transitive taint analysis of the full executable. Generic
terminal/encoder inline instances, every allocator/stdlib/error path, dynamically
linked libc/OS and all dependency callbacks do not have a complete instruction
classification here. B cannot be inspected at all. The requested *complete
two-artifact* V373 audit therefore remains incomplete. The checked N1 finding
and B build failure are the stop/handoff facts; neither is hidden by the broad
inventory. No absence-of-leakage claim is made.

## Hashing internals and signing arithmetic (A)

`HOST_HASH` reaches `aspis_prover::host_hashv 0x117a50–0x117daf`.
The expander calls it through the function pointer supplied at A planner
`plan.rs:116`; salt derivation `0x118c10–0x118e73` hashes the retained private
leaf seed with public attempt/context/tree/index fields. Seed derivation,
private expander blocks, salted leaf contents and witness-derived commitment
messages therefore reach SHA's actual compression, not just a wrapper.

| Body | Branch/address review | Classification / rows |
|---|---|---|
| SHA-256 wrapper `0x117a50–0x117daf` | Input segment count/length and buffer position drive branches (`117aa5`, `117b06`, `117b53`, `117c85`, `117cac`). Byte contents enter state only. Public grammar fixes segment lengths at seed/salt/leaf callers; rejection history changes how often refills call it. Padding address uses length-derived buffer position, not a secret message byte. | clean for fixed public lengths; refill call count R2/R5; V354/V359/V360/V373/V371 |
| SHA-256 dispatch/software `0x194660–0x197282` | `194685/194693/19725b` read cached CPU-feature state; initialization calls CPUID `0x197290–0x1972d4`. Software block loop `1946d0/1971ed` depends only on block count/pointer end. The unrolled compression uses fixed block offsets, fixed stack slots and RIP-relative constants; no secret-indexed round table observed in this body, and no DIV/IDIV. | clean in reviewed compression body for fixed block count; V371 remains |
| SHA-NI `0x1972e0–0x19769c` | Exactly two Jcc: empty block count `19730a`, next block `197670`. Round constants use RIP-relative fixed loads; message loads `[rsi+0/10/20/30]`; PSHUFB masks are fixed constants, not secret table indices. SHA256RNDS2/MSG1/MSG2, shuffle and add operations execute fixed round sequence; no DIV/IDIV. | clean fixed-block schedule/addresses; V371 still substantive |
| Poseidon base round `0x164d40–0x166879` | Branches `164d51/165876/165d37` select public round class/index; `165039/16602d` loop over fixed lanes. Constants indexed by public round/lane; state bytes are arithmetic operands only. | clean in reviewed round body; V373/V371 |
| Poseidon traced sponge `0x166880–0x16ad9a` | Arity/chunk branches `1668c3`, `166944`…`166a4f`; fixed round loops `16754a/167de9/16834b/168685/168edd` and final sponge loops `1693fa/169cc6/16a208/16a51a/16ad6c`. Round/lane arithmetic selects constants; public arity controls chunk count. No secret-state lookup indices observed. | clean reviewed base sponge schedule at fixed public arity; V373/V371 |
| Poseidon node compression `0x16ada0–0x16d2b6` | Five Jcc `16b8ef/16c190/16c6e7/16c9ff/16d27b`, all fixed lane/round counters. Fixed two-digest input/output offsets. Trace-round pair `0x16d2c0–0x16dc67` uses public local-row/round index. | clean in these bodies, secret IMUL/SIMD/selection timing retains V371 |
| SHA-512 for secret-key expansion/signing | `ExpandedSecretKey::from 0x18c560–0x18c6b9` has no Jcc. Compression software `0x197790–0x19b2cb` has only block-count/end branches. AVX2 `0x19b2d0–0x19be63` uses public block count/fixed round loops and public CPU-feature dispatch (`compress512 0x1976a0–0x1976eb`). Signing wrapper's SHA buffering branches use public message length and fixed-size secret prefix. | reviewed compression schedule/addresses clean for fixed lengths; V373/V371/V396; N7 input parsing remains |
| Ed25519 scalar/basepoint path | `mul_base 0x18f3e0–0x18fa14` calls radix conversion with **public w=4** (`18f409`); only fixed odd/even digit passes select table number. `LookupTable::select 0x190140–0x19041b` has no Jcc: all eight candidates are loaded at fixed offsets and selected by SETcc/conditional assignment (`0x194160…`, no Jcc). Private digit does not index a point address in this body. | clean reviewed table-selection body + V371; not a whole signing/storage proof |

SHA and Poseidon schedule findings are restricted to named reviewed bodies and
public-length provenance, including any repeated invocations. They do not prove
ROM behavior, freshness, collision assumptions or whole-call joint simulation.
No CPU mode or runtime dispatch was experimentally forced. DOITM OFF remains
D248 host evidence; V371 covers secret-data ALU/MUL/IMUL/SIMD/SHA/compare/select/
shift timing. Even a branchless/hash-instruction body does not discharge it.

### Explicit DIV inventory (variable-latency operations)

A's selected symbol inventory has DIV in these bodies. Every occurrence is
retained with PC and divisor in `A/inventory.json`; no selected IDIV was found.
The listed metadata provenance is from source and callers, not a CPU timing
proof. No observed selected DIV uses a raw private field limb as its operand.

| Body / DIV PCs | Operand provenance / row |
|---|---|
| multiproof::node_count `b20a9 div cl` | 18/(2*t+1), public tree depth; query node selection retains V359 |
| cert-build::eqw `1057b2/105a07` | Boolean row index divided by fixed powers-of-two table; V363 |
| cert-build::pgv `105b65/105b87/105b92/105bb0/105be0/105bea` | public degree/index combinatorial coefficient arithmetic, not polynomial value; V363 |
| cert-build::pfac `106807/10693c`, bterm `107303/107312`, rr_ent `109142/10914f` | row/descriptor/degree bits via public dimension/power tables; field coefficients are multiplied afterwards; V363 |
| cert-check::nvec_ok `114214` | certificate pivot index modulo public matrix width; certificate/challenge provenance/joint law V364 remains |
| Scalar::as_radix_2w `1919c1/1919d7` | (255+w)/w for public window w, generic fallback; main signing basepoint caller passes w=4 and takes the specialized no-DIV path (`1917d2` not taken); V373/V396 |

A's sumcheck does not contain the example's parallel assignment-index DIV: the
recipe does not enable the CT/parallel feature. The supplementary example's
DIV addresses and latency claims are not transferred to A or B.

## Status and handoff

**V373 remains OPEN / P. V374 remains OPEN / P.** A has checked native findings
and named-body coverage; B has a checked build-reproducibility failure and no
binary. This is not completion of the requested transitive two-artifact audit.
The exact branch/source/build identities, all 26 changed and six missing files,
reviewed sites and unreviewed closure limits are retained. N1 specifically needs
a lead assessment beyond the D268 final poleBad classification.

Before/after `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` and its
deployment premises: unchanged. No formal premise removed, added, weakened or
moved into T. V352–V364 joint native obligations, V370 compiler preservation,
V371 CPU latency, V373 and V396 client binding remain. No source under crates/,
programs/ or any candidate/soundness file was edited. No Lean theorem or new
axiom was introduced. Budget: 0/30 Lean (not useful to the checked native branch
or stale-lock failure); 0/0 Kani. No task key or account was generated, accessed,
deleted, burned or unlinked.

Next concrete deliverables: lead obtains corrected/pinned B lockfile revision,
confirms adoption features/64-byte client route and exact toolchain, then rebuilds
and audits that binary including the unresolved inline/dependency edges. The
[V374 plan](V374-PLAN.md) requires its resulting SHA and a lead-scheduled quiet
window; it is proposed only and explicitly blocked for the unbuilt B. No timing
sample was taken. No absence-of-leakage claim is made. **Target not yet established.**

Validation and resource closure: `dual/validate.py` passes source-context,
instruction-PC, both-source identity, failed-B/no-binary, 26/6 comparison,
limits/swap and cleanup bindings. This is an artifact consistency check, not a
CT theorem. The pre-existing packet validator also passes for its separately
labelled diagnostic example; it does not validate this new binary.
`git diff --check` passes after trimming presentation-only trailing spaces in
the selected excerpt (the full raw objdump hash is unchanged).

Five scopes were sequential: A build, B failed build, initial A extraction,
expanded signing/parser A extraction, final source/hash validation. All 6G/8G/
swap0/Tasks64; no refusal or quiet-window bypass. `resource-summary.json`
records exact target, revision, exit, wall, GNU-time RSS and swaps where captured,
and cgroup peak/swap for all runs. Initial extraction had no GNU-time wrapper:
its process peak RSS was not captured; the 237,322,240-byte cgroup peak is retained
and is explicitly not relabelled RSS. The expanded extraction has a GNU-time
receipt. No result here is a formal release result; `#print axioms` is N/A for
all native work. This missing initial process-RSS metric is retained honestly.

Post-build source validation found zero changes in all 1,295 A files and 1,303
B archive files, including every pinned A file and B's unchanged standalone
lockfile. Both job-owned Cargo target directories (`target`, `dual-target-A`)
were removed after retaining A binary/full-disassembly hashes and excerpts;
`cleanup.json` confirms removal. B never produced a binary. Retained binaries
remain outside git; no binary, key, Cargo target, `.olean` or archive is committed.

The B correction request is pending with the lead; no unapproved revision or
lockfile change is inferred from elapsed time. Stop here on the checked N1
source/machine finding and exact B build failure, with the full audit still
OPEN, rather than spend Lean attempts on an unrelated theorem.
