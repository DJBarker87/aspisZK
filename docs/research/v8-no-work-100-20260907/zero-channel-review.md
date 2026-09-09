# Complete V8 transactions below 1.2M: zero-page and channel fusion

2026-09-09. Continues [complete-performance-review.md](complete-performance-review.md)
from `b9630a7099cb533ff559770db81a7a8a55ee18ba`. No production source,
default, manifest or main-branch change. The Solana testing skill guided the
matched runtime and negative/atomicity checks. All overlays ran in the existing
task-owned NUC source copy; concurrent main work was preserved.

## Measured result

**All four complete transaction shapes now pass an actual 1,200,000 CU
TransactionConfig limit**, including three maximum-body proofs per shape.
These are genuine payment proofs through authenticated ASQ8 → ASF8 → repaired
V8 → ASR8 → atomic Pool settlement, not isolated verifier totals plus estimates.

| Complete shape | Previous maximum-body maximum | Chunked page scan | Plus channel fusion, bundled P-Token | Plus channel fusion, SPL Token 3.5 control |
|---|---:|---:|---:|---:|
| Transfer, current page | 1,170,650 | 1,170,637 | **1,156,949** | **1,156,949** |
| Transfer, rollover | 1,244,066 | 1,183,174 | **1,169,440** | **1,169,440** |
| Withdrawal, current page | 1,182,365 | 1,182,352 | **1,168,551** | **1,174,591** |
| Withdrawal, rollover | 1,256,466 | 1,195,574 | **1,181,866** | **1,187,906** |

Each entry is the maximum of three fixed, previously generated 40,282-byte
proofs, with both frontiers at their 296-node body cap. **They are observed
maxima, not an all-statements/all-PDA-bumps/all-schedules CU theorem.** The
remaining measured headroom is 18,134 CU with P-Token, 12,094 with SPL Token 3.5.
The body and transcript are unchanged; no new hint, nonce, scalar or opening
is transmitted. Earlier structured/fused-row/inversion gains are already in
the first column and are not counted again.

[Machine-readable results](zero-channel-results.json),
[pins/commands/resources](zero-channel-evidence.json),
[exact reconciliation](experiments/audit_zero_channel.py).

The original no-regression requirement remains **unmet**. Re-running selected
V7 with the same optimised Pool, Registry, runtime and pinned SPL Token 3.5 gives
1,040,823 / 1,034,401 / 1,036,365 / 1,048,884 CU in table order. The respective
V8 observed maximum excesses are **116,126 / 135,039 / 138,226 / 139,022 CU**.
V7 still uses one frozen strict proof per shape and its original workspace
release policy; V8 uses the research standalone checked-arithmetic policy.
This is not a same-query comparison or a release certificate.

## 1. The rollover cost was a complete bytewise zero scan

The selected Pool source's `account_is_zeroed_program_page` checks owner and
exact length, then `data.iter().all(|byte| *byte == 0)` over **8,256 bytes**.
Rollover invokes this on the caller-supplied fresh history page before verifier
CPI. The selected old-page invariant optimisation was already enabled; this
is a different check, and it must still inspect every fresh-page byte.

The replacement reads 1,032 little-endian u64 chunks and tests each for zero,
then checks every remainder byte for arbitrary slice lengths. It uses safe
`chunks_exact(8)` and `from_le_bytes`; no alignment, honest-account, canonical
field or pre-zeroed-memory assumption is introduced. Owner, length, writable,
PDA, borrow and all settlement checks remain in the original path.

Instrumented intervals, including the same logging schedule:

- Bytewise scan: **66,267 CU**.
- Chunked scan: **5,387 CU**.
- Interval difference: **60,880 CU**; complete instrumented difference 60,881.
- Actual uninstrumented same-proof complete rollover saving: **60,892 CU**.
  Current-page paths change by 13 CU from code generation/layout; do not book
  this as a skipped current-page check.

`ZeroPage.lean` proves the LE encoding is zero exactly when all bytes are zero,
proves the eight-byte encoding is below 2^64, and proves the recursive
take-eight/drop-eight scan equals the bytewise predicate for every byte list.
The remainder and empty list are part of the theorem. These are source-shaped
list/integer identities, **not a translated Rust/std/SBF theorem**.

The actual Rust helper passed all 8,256 × 255 one-byte corruption cases,
unaligned subslices, short lengths, remainders and deterministic multibyte
comparisons. Complete SBF tests rejected 24 representative corrupt positions
per operation—including all eight final bytes—with **the same error as the
old Pool**, no verifier CPI and byte-exact rollback. There are 48 old/fast
rejection pairs, not a universal SBF input enumeration.

Artifacts: [zero_page.rs](experiments/zero_page.rs),
[ZeroPage.lean](experiments/ZeroPage.lean),
[Pool overlay](experiments/pool-zero-page.patch),
[negative harness overlay](experiments/pool-zero-driver.patch),
[raw evidence](evidence/zero-page/).

## 2. Fuse nine Karatsuba channels before canonical reduction

The selected shared dot-product reconstruction reduced nine raw u64 channels
to canonical M31, reconstructed three CM31 products, then reconstructed QM31.
Its linear reconstruction allows reduction to move to the **four final limbs**.

Let the partially folded channels be `[[a,b,c],[d,e,f],[g,h,i]]`, with
`fold(x)=(x & p)+(x>>31)`, p=2^31−1. The four unreduced results are:

```text
a + 3d − b − e − f
c + 2f − a − b − d − 3e
g + b + e − h − a − d
i + a + b + d + e − g − h − c − f
```

Add 32p to each before the subtractions, then apply the existing full M31
reducer once per result. Every raw u64 partially folds to at most **5p+3**;
the largest negative sum is at most 30p+18 < 32p. Every positive prefix is
at most 57p+15 < 2^64. Thus the wrapping Rust operations implement ordinary
integer arithmetic here, without an overflow/underflow acceptance assumption.

The symbolic Lean development proves the ring reconstruction, partial-fold
congruence, exact raw range, padded-prefix bounds and whole four-output modular
congruence. It reuses the existing small symbolic facts; it does not enumerate
QM31 or unfold generated certificates. The first attempted **weaker premise**
`a_i<6p` did not justify 32p padding for six negative terms. Lean rejected it;
the retained proof derives the actual tighter cap from arbitrary u64 inputs.
An overly broad modulo `simp` also failed and was replaced with explicit
`Int.ModEq` composition. Failed logs are retained, not counted as proved results.

Actual patched Rust passed independent i128 modular reconstruction for 512
zero/max raw-channel arrays and 8,192 deterministic arbitrary-u64 arrays,
alongside the existing field/product/parser controls. Same-proof complete
transactions save **13,651–13,801 CU** on the maximum-body set, with no parser,
challenge, response or authentication change.

Artifacts: [QmCrossRange.lean](experiments/QmCrossRange.lean),
[channel overlay](experiments/qm-channel-partial.patch),
[independent controls](experiments/range_kernel_controls.rs),
[final axiom audit](experiments/qm-group-lean.log),
[raw evidence](evidence/channel/).

## 3. A tested non-winner and a Token-accounting correction

The same partial-reduction idea was tested for the six/seven-product grouped
kernels. The algebra and range proofs pass, and complete transactions have
**exactly zero additional CU saving**. These entry points are not used by the
active selected V8 path (`dot6` has only field-test callers; `dot7` serves the
older degree-72 radix-eight evaluator). The different control ELF is retained
as evidence, but the winning build does **not** enable `v8_qm_group_partial`.
Next time, establish the active call site before an extra SBF build.

The older harness's label **“legacy SPL Token builtin” was imprecise**. Pinned
LiteSVM 0.16.0 `src/programs/mod.rs::load_default_programs` loads bundled SBF.
`LiteSVM::new()` selects its frozen mainnet-feature table, including its P-Token
replacement entry. This is a property of this pinned local runtime, not an
independent claim about a deployed cluster's present feature gates.

We added explicit, hash-checked loader controls using the cached bundled
P-Token and SPL Token 3.5 ELF files. Explicit P-Token reproduces every previous
CU exactly. SPL Token 3.5 adds exactly **6,040 CU per withdrawal**, while all
four shapes still pass 1.2M. Both execute actual SBF Token CPI; no native mock
is being priced as a production token program. Withdrawal-CPI-failure cases
remain a separately labelled deliberate failing-program double.

## Evidence and unchanged obligations

| Result | Evidence status / exact boundary |
|---|---|
| All-byte zero-scan equivalence | Kernel-checked finite-list/integer theorem; differential actual Rust; matched malformed SBF rejection |
| Nine-channel reconstruction | Kernel-checked algebra, range and modular congruence; actual patched Rust/independent integer oracle |
| Complete cryptographic and settlement path | SBF measured, same proof bytes, canonical grammar and binding; original successful atomicity assertions |
| Four-shape 1.2M target | All measured ordinary/max-body controls pass actual cap; not universal CU coverage |
| No regression vs selected V7 | **Not met** under the matched controls |
| Global recovery / FS / full-view ZK | Unchanged unresolved obligations; no new numerical security certificate |

Focused Lean leaves exited zero with only `propext`, `Classical.choice` and
`Quot.sound`, no new axioms or `sorry`. Zero-page proof: 15.14 s, 2,823,749,632 B
peak RSS, zero swap. Final extended arithmetic leaf: 2.54 s, 2,862,809,088 B,
zero swap. Rust controls were optimised, with overflow checks for the field
test build. Capped NUC SBF builds took roughly 33 s and at most 588,688 KiB
reported process RSS, zero swaps. Cgroup caps also bounded aggregate memory.
Exact commands, source hashes, exits and axiom logs are linked above.

Direct r10 displacement scans of the **actual winning stripped verifier and
Pool ELFs** find no offset above 4,096. Stripping removes most names: this is
not a proof about all machine-pointer accesses, cumulative call stacks or
Rust-to-SBF correspondence. The builds emit no new stack-size warning.

No prover rerun was needed: verifier/Pool-only arithmetic changes accept the
same archived proofs. The prior 3.17-second/197.71-MiB NUC producer measurement
is inherited evidence, not a newly measured distribution for a changed prover.
Nothing was uploaded to a third-party research service; all fixtures are
synthetic and no witness or owner secret is printed.

No cryptographic error term changes: these are deterministic rewrites, not
new rounds, field choices or query distributions. The 40,282-byte census is
still `697*16 + 52 + 24 + 22*621 + 2*296*26`. Work/nonces earn zero security
credit. Mathematical computation equivalence excludes differences caused
solely by exhausting a CU budget: fitting a previously over-budget valid
transaction is the intended performance improvement.

## Reproduction and decision

On the existing task-owned NUC copy, with the predecessor integration installed:

```text
bash experiments/run_pool_zero_nuc.sh prepare NEW_LOG
bash experiments/run_pool_zero_nuc.sh test NEW_LOG
bash experiments/run_pool_zero_nuc.sh fast NEW_LOG
bash experiments/run_pool_zero_nuc.sh prepare-driver NEW_LOG
bash experiments/run_pool_zero_nuc.sh prepare-token NEW_LOG
bash experiments/run_complete_build_nuc.sh driver NEW_LOG
bash experiments/run_channel_nuc.sh prepare NEW_LOG
bash experiments/run_channel_nuc.sh test NEW_LOG
bash experiments/run_complete_build_nuc.sh channel NEW_LOG
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_TX_LIMIT=1200000 \
  bash experiments/run_complete_matrix_nuc.sh channel NEW_DIRECTORY
ASPIS_V8_CHANNEL=1 ASPIS_TOKEN_CONTROL=legacy35 ASPIS_TOKEN_ELF_DIR=<pinned ELF directory> \
  bash experiments/run_pool_zero_cases_nuc.sh cap1200-max NEW_DIRECTORY
```

Here `experiments` means `docs/research/v8-no-work-100-20260907/experiments`.
Preparation scripts require exact predecessor hashes and refuse real Git
worktrees or already-changed unknown sources; do not reset to make them run.
All job wrappers impose no-swap memory limits, offline cached builds and fresh
evidence paths. The Token ELF directory and hashes are recorded in raw JSON.
The host replay is `python3 experiments/audit_zero_channel.py`; it recomputes
the stored rational/integer census and reconciles actual transaction evidence.

**Keep the chunked fresh-page scan and four-limb channel reconstruction. Do
not count the grouped-kernel control as a saving.** This continuation closes
the measured four-shape 1.2M milestone with the same proof body, but neither
exhausts optimisation nor establishes production readiness or V7 parity.

The next deciding experiment is a **same-input profile of shared semantic/copy
selector preparation in the winning complete verifier**, then one exact
shared-factor rewrite tested against the four complete shapes. That is where
to seek the remaining 116–139k CU parity gap; another inactive-kernel rewrite
or an assumed worst-case bound would not address it. Separately, an
all-reachable accepted CU argument must cover statement/PDA and schedule
variation before the measured margin can be called a guaranteed ceiling.
