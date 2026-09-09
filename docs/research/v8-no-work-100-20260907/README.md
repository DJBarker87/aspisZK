# V8 no-work 100-bit research — decision and reproducible prototypes

Latest: [expanded quotient fold with shared reductions](quotient-fold-review.md).
Worst observed complete transaction is **1,092,138 CU**, with **107,862 CU**
headroom under the actual1.2M cap and the same **40,282-byte** body. The
Lean-proved rewrite saves another55–102 CU on the twelve maximum proofs;
ordinary/rollback controls and selected-arithmetic tests pass. See
[results](quotient-fold-results.json) and the separately labelled
[fresh stage profile](line-profile-review.md). Same-pool V7 is still cheaper.

Previous: [reuse the checked line coordinates](line-norm-review.md).
Worst observed complete transaction is **1,092,232 CU**, with **107,768 CU**
headroom below the real 1.2M cap and the unchanged **40,282-byte** body.
The source-shaped Lean proof includes the literal half-word range/field bridge;
all 50 maximum/ordinary/rollback cases pass. See [results](line-norm-results.json).
Same-pool V7 remains 20,089–43,348 CU cheaper; universal CU remains open.

Preceding retained changes: [split-prefix inversion fusion](inversion-fusion-review.md),
[circle norm](circle-norm-review.md), [chord norm](chord-norm-review.md),
and [authentication order](auth-order-review.md). Each reports its separate
measured delta; rejected controls are not included in the selected build.

Previous: [direct decoder blocks and rejected gamma fusion](decode-controls-review.md).
The Lean-backed decoder saves **1,320 CU** per complete maximum-body proof.
Worst observed is **1,100,125 CU**, with **99,875 CU** headroom below the real
1.2M cap and the unchanged **40,282-byte** body. Malformed/ordinary/rollback
controls pass. Four-channel fusion regressed by **24,882 CU** and is not selected.
See [results](decode-controls-results.json); V7 parity and universal CU remain open.

Previous: [contiguous C2 leaf records](leaf-record-review.md).
The Lean-proved literal record-slice rewrite saves another **88 CU per complete
proof**. Worst observed is **1,101,445 CU**, with **98,555 CU** headroom below
the real 1.2M cap. Body remains **40,282 bytes**; same-proof, malformed and
rollback controls pass. See [results](leaf-record-results.json).
V7 parity and universal CU coverage remain open.

Previous: [byte-equivalent Merkle inputs and borrowed digests](merkle-input-review.md).
The combined implementation saves **12,472–12,502 CU** on identical complete
maximum-body proofs. Worst observed is **1,101,533 CU**, with **98,467 CU**
headroom below the real 1.2M cap. Lean proves the byte-input identity; raw-byte,
small-tree, full-transaction and rollback controls pass. The ELF shrinks and
the body stays **40,282 bytes**. See [results](merkle-input-results.json).
V7 parity and universal CU coverage remain open.

Previous: [fixed-width gamma dots](gamma-fixed-review.md).
Another exact rewrite saves **13,761–13,779 CU** on identical complete
maximum-body proofs. Worst observed is **1,114,035 CU**, with **85,965 CU**
headroom under the real 1.2M cap, including pinned classic Token settlement.
The seven-chunk sum/range interface is Lean-proved; canonicality, ordinary,
malformed and rollback controls pass. Body remains **40,282 bytes**.
See [results](gamma-fixed-results.json); V7 parity and universal CU remain open.

Previous: [fixed tag-offset plans](tag-offset-review.md).
The Lean-backed straight-line rewrite saves **6,007 CU** on each identical
complete maximum-body proof. Worst observed is **1,127,798 CU**, including
pinned classic Token settlement, with **72,202 CU** headroom under the real
1.2M cap. Body remains **40,282 bytes**; ordinary, malformed and rollback
controls pass. See [results](tag-offset-results.json). A fresh profile identifies
canonical/gamma reconstruction and internal authentication as larger remaining
targets. No new heap, proof or transcript data; V7 parity and universal CU remain open.

Previous: [shared tag sums across kernels](tag-shared-review.md).
Reusing the generated selector plan saves a further **4,030–4,044 CU** on
identical complete transactions. Worst observed is now **1,133,805 CU** at
the real 1.2M cap, with the unchanged **40,282-byte** maximum body. Lean proves
all thirty sums and the necessary reduced-sum interface; actual-source and
malformed-proof/rollback controls pass. See [results](tag-shared-results.json).
No extra heap, proof or transcript data; V7 parity and universal CU remain open.

Previous: [range-proved tag-prefix splitting](tag-split-review.md).
One further exact rewrite saves **3,754–3,773 CU** against the shared-copy build.
Worst observed complete transaction is now **1,137,838 CU**, including pinned
classic Token settlement, with the unchanged **40,282-byte** maximum body.
The ordinary checked version regressed and is retained as a rejected control;
the selected version removes only proved redundant accumulator overflow checks.
Malformed-proof and atomic rollback tests pass. See [results](tag-split-results.json)
and [artifacts](tag-split-artifacts.json); universal CU, V7 parity and global
security remain open.

Previous: [shared copy-selector assembly](scatter-performance-review.md).
A generated, Lean-proved public addition plan saves another **39,090–39,208 CU**
on identical complete maximum-body proofs. Worst observed is **1,141,606 CU**
including pinned classic SPL Token settlement, at the actual 1.2M cap.
The body stays **40,282 bytes**; malformed-proof and atomic rollback controls
pass. These are fixture maxima, not a universal bound; selected-V7 parity and
global security remain open. See [results](scatter-performance-results.json)
and [evidence](scatter-performance-evidence.json).

Previous: [shared copy windows and range-certified tag accumulators](copy-performance-review.md).
Two further Lean-backed rewrites save **7,072–7,118 CU** on identical complete
maximum-body proofs. All four shapes pass the actual 1.2M cap; worst observed
is **1,180,814 CU**, including the pinned classic SPL Token 3.5 SBF settlement.
The body remains **40,282 bytes**. These are measured fixture maxima, not a
universal CU bound or production-readiness claim. See
[results](copy-performance-results.json) and [evidence](copy-performance-evidence.json).

Previous: [complete transactions below 1.2M: page scan and channel fusion](zero-channel-review.md).
All four shapes pass the actual **1.2M TxV1 limit** with 40,282-byte proofs.
The worst observed complete transaction is **1,181,866 CU**, or **1,187,906 CU**
with the separately pinned SPL Token 3.5 SBF control. New Lean equivalence/range
proofs justify the rewrites; all-byte rejection and atomic rollback controls pass.
These are measured fixture maxima, not universal CU bounds. Selected-V7 parity
and global security remain open; production is unchanged.
See [results](zero-channel-results.json) and [commands/evidence](zero-channel-evidence.json).

Previous: [complete transactions and QM31 arithmetic](complete-performance-review.md).
Maximum-body current-page transfer / withdrawal now pass at **1,170,650 /
1,182,365 CU** worst observed; rollover remains **1,244,066 /1,256,466 CU**.
These execute actual account authentication and atomic Pool settlement.
At that checkpoint the all-shapes 1.2M target and selected-V7 parity remained unmet. Host proving
is **3.17s mean +1.43s shared setup /197.71 MiB RSS**, with byte-identical proofs.
See [exact results](complete-performance-results.json); production is unchanged.

Previous: [range-proved arithmetic and sparse fusion](range-performance-review.md).
The quiet isolated verifier accepts three **maximum-frontier, 40,282-byte**
proofs at **1,194,675 /1,194,522 /1,194,670 CU**, with a 1.2M limit.
Ordinary no-search proving is **3.59 seconds mean /197.91 MiB peak RSS**.
Overflow checks remain enabled; explicit bounded kernels and new Lean
identities replace blanket overflow-off controls. No complete-transaction
CU parity, global security completion or production activation is claimed.
See [results](range-performance-results.json) and
[commands/evidence](range-performance-evidence.json).

Previous: [structured CU rescue and basis alignment](structured-performance-review.md).
Both structured families, fused z/XOR12 rows, shared arithmetic and exact
query kernels reduce the checked isolated verifier to **1.888–1.890M CU**.
Proving remains about **4.02 seconds /198 MiB** on the NUC.
Separate unselected core-only/global overflow-codegen controls reach
**1.325–1.327M /1.296–1.298M CU**; adopting those requires the indicated
range/source audit. No complete-transaction CU parity is established.
The body cap stays **40,282 bytes**. See
[results](structured-performance-results.json) and
[commands/evidence](structured-performance-evidence.json).

Previous: [NUC proving-time and dense SBF prototype](performance-review.md).
Three genuine research proofs take about four seconds each on the NUC.
The isolated SBF verifier completes at 7.31–7.32M CU under a diagnostic cap,
and fails the ordinary transaction budget. This is a measured implementation
bottleneck, not CU parity or a production-ready security claim.

Latest: [raw C1 recovery and the circle polynomial bridge](raw-c1-review.md).
A genuine accepted transfer with two noncanonical unopened C1 fibres defeats
the strict graph extractor but yields a checked witness through byte-preserving
extraction and totalized error correction. Lean now proves the universal natural
tensor/degree bridge and the finite-check-to-global-image implication. All-domain
source factors pass; universal source/Gao and global security gates remain open.
See [results](raw-c1-results.json) and [commands/evidence](raw-c1-evidence.json).

Latest: [C1 query-graph extraction and error correction](query-graph-review.md).
Frozen hash-query access replaces the extra-opening oracle. An accepted genuine
payment defeats two fixed coefficient windows; Gao-style correction extracts a
checked witness from that SAME proof. A 16,535-corrupt-fibre control also recovers
coefficients. New Lean one-fibre recovery and an exact conditional sampling ledger
advance extraction, without establishing global security, FS, ZK or CU parity.
See [results](query-graph-results.json), [sampling conditions](c1-sampling-results.json)
and [commands/evidence](query-graph-evidence.json).

Latest: [same-execution authenticated C1 / payment extraction](payment-extraction-review.md).
Four genuine honest payment proofs pass the repaired research grammar and yield
checked witnesses from an explicit extra-opening oracle. All four D-corrupted
arms hit one changed fibre and reject; no accepting seed was searched for.
New Lean mask/read and path-residual prerequisites pass. Actual replay access,
corrupt-C1 recovery and universal validator coverage remain open. See
[results/access census](payment-extraction-results.json) and
[reproduction/evidence](payment-extraction-evidence.json).

Latest: [beyond-radius recovery continuation](radius-residual-review.md).
The 9,302-corruption boundary can lose the 9,301 classifier while retaining a
unique nearest anchor; the repaired relation suffix accepts missed-corruption
schedules. New Lean claim-transport identities and an executable recovered-C1
to checked-transfer-witness endpoint narrow the source obligations. Full
payment embedding and accepted residual recovery remain open. See
[exact ledger](radius-results.json) and [commands/evidence](radius-evidence.json).

Latest: [near-anchor gamma-cover continuation](near-gamma-review.md).
The new Lean construction supplies a pre-gamma component tuple covering every
9,301-close original-code candidate and at least 245,609 fibres of own support.
A supported-event gamma/row theorem permits gamma-dependent corrupt supports.
The ideal local ceiling is 105.145190 bits at the unchanged 40,282-byte body;
no-near-anchor and tuple-to-payment extraction remain open. See the
[exact ledger](near-gamma-results.json) and [replay evidence](near-gamma-evidence.json).

Latest: [ordinary point/inactive binding continuation](row-binding-review.md).
An executable false-point-claim construction passes the unshifted semantic and
image-aware research relation suffix, including non-polynomial received words.
A byte-neutral row-weight shift has a checked joint noisy-word bound without
`inactiveExact`; component recovery, full-view ZK, FS and matched CU remain
open. See [exact ledger](row-binding-results.json) and
[commands/axioms/measurements](row-binding-evidence.json). Production unchanged.

Latest: [non-polynomial recovery continuation](robust-recovery-review.md).
A new Lean bounded-corruption game covers bad anchor boundaries and adaptive
off-anchor finals without assuming the received word is polynomial. At B=9301
the local error is 105.1452784160 bits; no-close-anchor and good-anchor/same-final
unextracted mass remain unbounded. An isolated complete relation suffix now
checks real canonical/Merkle openings and carried image weights, but is not a
payment verifier or CU/ZK certificate. See [exact ledger](robust-results.json),
[evidence and commands](robust-evidence.json). Body maximum remains 40,282 bytes.

Latest: [joint image/relation review](joint-image-review.md). A new Lean causal
game proves the restricted exact-polynomial/invalid-image bound, 118.4150 bits
at q22 under ideal sampling, including adaptive finals and sequential responses.
The pinned V8 kernels do not install this gate. Research-only prototype/checks
pass; source integration, non-polynomial recovery, full-view ZK and full CU
remain unresolved. See [exact ledger](joint-image-results.json) and
[replay evidence](joint-image-evidence.json). No production change.

Latest: [adaptive query-boundary review](adaptive-tail-review.md). Source timing
permits a prefix-defined mathematical width29 event. A pre-OOD T_512 oracle
nevertheless gives perfect V8 chord-query agreement outside the original code:
image/relation accounting is indispensable. This is not actual full acceptance
or a claimed H_width29(T)=1. The adaptive upper bound remains open.

Latest continuation: [Lean repair ZIP review](lean-repair-review.md). The generic
fixed-target query-support theorem and root-product instance are kernel-checked;
the actual adaptive discarded-branch coverage remains unresolved. All supplied
finite checks reproduce. Tag-73's general prior-plus-query batch costs q roots,
not automatically q-1. See [exact results](lean-repair-results.json) and
[formal/execution evidence](lean-repair-evidence.json).

Latest continuation: [recovery ZIP review and adaptive-cover investigation](coverage-review.md).
All 46,875 supplied cases and new q23/quintic controls reproduce. A focused Lean
result now constructs a <=100 joint-tuple family at the relaxed 38,228-symbol
floor, plus C1 descent from the tuple's own support. This admits the known
counterexample's zero tuple but **does not prove adaptive branch coverage**.
q23 remains an unapproved 41,527-byte control; full quintic q22 is the
42,984-byte better-margin field-port control. See [exact rows](cover-results.json)
and [execution/source evidence](coverage-evidence.json).

**Current decision:** [decision.md](decision.md). No investigated implementation
meets every requirement. A new full-fibre counterexample rejects extending the
2,800-root fixed-family bound to unconditional recovery even after both agreement
gates. The current 40,282-byte q22 certificate is not established. This is not a
sub-100-bit forgery or a proof that a repaired protocol is impossible.

[joint-results.json](joint-results.json) records the new optimized Rust checks,
14,739 tiny exhaustive query cases, 255 fold cases and eight axiom-free finite
Lean arithmetic facts. The fixed-target query-aware bound is promising but does
not establish adaptive target existence. Primary research remains QM31 q22;
the better-margin fallback control is quintic q22 (+2,702 bytes), while quintic
q21 remains the thin-margin control (+1,410 bytes).

Latest decisive finding: [recovery-counterexample.md](recovery-counterexample.md)
refutes the unconditional 28-gamma recovery shortcut. The 99.246-bit isolated
boundary is not a full-protocol attack. See the exact Rust/Python construction
and small Lean arithmetic certificate; old conditional model figures are not
upgraded to security claims.

The supplied prototype ZIP has now been independently reviewed and reproduced:
[zip-review.md](zip-review.md). Its actual four-fold block contraction is correct
in the checked scope. A production-field Rust implementation agrees on 160
terminal values and counts 91 generic products including the outer scale.

Latest engineering result: [grouped-mask.md](grouped-mask.md) extends the fast
path to actual grouped binary masks (142 generic + 170 mixed products), with
2080 mask cases and 20 aggregate relation tests. Full security/CU remain open.

Start with [report.md](report.md). See [security-contract.md](security-contract.md),
[baseline.md](baseline.md), [ledgers-and-candidates.md](ledgers-and-candidates.md)
and [sources.md](sources.md) for the contract, pins, applicability and primary sources.
[candidates.json](candidates.json) retains exact rationals and flags;
[candidates.csv](candidates.csv) is the compact index. Unmeasured is never zero cost.

Continuation: the user accepted 40,282 bytes. [chord-verdict.md](chord-verdict.md)
records the exact full-dimension quotient prototype, algebraic derivation,
reverse-membership counterexample and revised research decision. It does not
upgrade the earlier conditional security figures to proved security.

Next continuation: [relation-link.md](relation-link.md) gives explicit sparse
membership constraints, the natural-tensor relation transpose, exact optimized
tests and host timing. Security composition and full-transaction CU remain open.

Branch: research/v8-no-work-100-20260907. Worktree:
`/Users/dominic/ZK/.worktrees/ZK-v8-no-work-100-20260907`.
Base: `4c91f97ac6576201f90d41c2a575e54c026e3796`. Date: 2026-09-07.
The research branch is committed and pushed at the user's request. No deployment,
remote build, production mutation, witness upload, paid infrastructure or subagents.
Concurrent main/V8 work was preserved.

Host: Apple M3 / Mac15,13, Darwin 25.5.0 arm64, 25,769,803,776 RAM bytes.
Rust/cargo 1.93.0. gh, Python3, jq, curl, pdftotext, cargo-build-sbf and elan
Lean/lake launchers are installed. These are not a cached Linux release build
environment. The repository's SBF workflow requires Linux x86_64, finite cgroup
limits and zero swap. No large build was launched. Standalone optimized Rust
avoided dependency rebuilds; executed jobs stayed far below 8 GiB.

## Reproduce from the worktree root

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/feasibility.py --test
python3 docs/research/v8-no-work-100-20260907/experiments/independent_fields.py
rustc --edition=2021 -O docs/research/v8-no-work-100-20260907/experiments/fields.rs -o /tmp/aspis-v8-fields
/usr/bin/time -l /tmp/aspis-v8-fields
rustc --edition=2021 -O docs/research/v8-no-work-100-20260907/experiments/schedules.rs -o /tmp/aspis-v8-schedules
/usr/bin/time -l /tmp/aspis-v8-schedules
rustc --edition=2021 --test -O -A dead_code docs/research/v8-no-work-100-20260907/experiments/production_field_tests.rs -o /tmp/aspis-v8-production-field-tests
/usr/bin/time -l /tmp/aspis-v8-production-field-tests
```

The schedule benchmark links macOS System/CommonCrypto; port its callback before
Linux use. Seeds are public/synthetic. It is not the complete verifier. Field
sampling timings exclude SHA/RNG generation and do not benchmark secure entropy.

From this research directory, verify the deterministic artifact:

```sh
set -o pipefail
python3 experiments/feasibility.py | diff - candidates.json
```

The exact DP counts q-subsets by frontier with left/right subtree convolution.
Independent checks exhaust depths 1–4, q up to five; verify binomial totals and
falling-product query arithmetic. Production probabilities use exact integers/
rationals; floating logs are display only. Exhaustion records preserve exact
base and power instead of thousands of decimal digits.

Field certificates use Rabin's criterion for X^5-X-6 and Euler's nonsquare test
for u in the pinned QM31 tower. Independent Python uses polynomial arithmetic
modulo p and the alternate quartic u^4-4u^2+5. Both certificates passed, as did
1000 extension arithmetic cases and all 32 production field tests. These are
executable certificates, not Lean formal proofs.

Logs under experiments/ retain timings/RSS/swaps. Final field prototype:
0.46 s / 1,671,168 B RSS; search 0.83 s / 2,015,232 B; production field tests
0.37 s / 3,063,808 B. All exit 0, zero swaps. Counters apply to execution, not
compilation or proving. Prior V8 Lean/rank/prover and V7 CU evidence is reused.

Development corrections: first standalone invocations had an incorrect relative
include, omitted edition=2021, and direct production-field testing lacked
`extern crate alloc`. Research wrappers corrected these without production edits.
Python initially hit its integer-string digit guard on the 64th-power output;
the exact base/power representation fixed serialization. An initial cap245
search was replaced with the correctly matched cap246 experiment. No heavy
job was retried with a larger memory cap.

## Status and bounded next work

- Gate 1: source/census/combinatorics completed; full theorem applicability and
  NI/privacy claims remain unresolved for every serious candidate.
- Gate 2: small fields, samplers, hints and hiding-falsifier prototypes executed;
  prior two-OOD rank evidence reused. No new dense elimination.
- Gate 3: not entered; cryptographic predecessors have not passed, and a matched
  Linux SBF environment is unavailable locally.
- Gate 4: no expanded protocol formalisation or release replay; small standalone
  arithmetic leaves were checked, with empty axioms. They are not a V8 theorem.

The chord and structured/grouped-weight experiments are complete in their stated
scope; do not repeat them unchanged. The next deciding gate is query-aware
adaptive recovery covering discarded provider branches, as defined in decision.md.
Only after security/privacy applicability passes should the stack-safe complete
V8 implementation and matched four-shape transaction measurements proceed.
