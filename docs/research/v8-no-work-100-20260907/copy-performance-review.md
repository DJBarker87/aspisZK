# Shared copy windows and range-certified tag accumulators

Research continuation of `32026b0a1dc139f2684dd9dad247901d8d5ecdd2`,
2026-09-09. Production files/defaults, main, proof grammar and transcript are
unchanged. This is an internal evaluation rewrite of the repaired research
verifier, not a new soundness argument.

## Measured outcome

Both new rewrites improve **complete** authenticated ASQ8/ASF8/ASR8 transactions,
including Registry checks and atomic Pool settlement. The Token control is the
explicit, hash-checked **classic SPL Token 3.5 SBF**, not a cheap mock or an
inference about a live cluster's feature gates.

| Complete shape | Previous channel kernel, maximum observed | New suffix + seven-tag kernel, maximum observed |
|---|---:|---:|
| Transfer, current page | 1,156,949 | 1,149,847 |
| Transfer, rollover | 1,169,440 | 1,162,334 |
| Withdrawal, current page | 1,174,591 | 1,167,477 |
| Withdrawal, rollover | 1,187,906 | **1,180,814** |

Each row covers three predetermined, already-archived maximum-body proofs.
Every success uses the actual **1,200,000-CU transaction cap**, without a
diagnostic runtime limit override. The worst observed margin is **19,186 CU**.
The ordinary-body control's maximum is 1,174,753 CU. These are observations,
not a universal bound over all statements, PDA bumps, samplers and accepted
schedules.

On identical proof bytes, suffix sharing saves **4,054–4,085 CU**;
seven-tag accumulation saves a further **3,009–3,041 CU**. Their combined
saving is **7,072–7,118 CU**. The maximum proof body is still exactly
`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282` bytes. No new fields, nonces,
rounds, public messages, inverses or prover search are required.

Matched selected V7 with the same Pool/Registry/runtime/Token remains cheaper:
the four maximum-observed differences are 109,024, 127,933, 131,112 and
131,930 CU. Its original release build policy is retained; V8 retains checked
overflow. **The stronger V7 no-regression requirement remains unmet.**

## What the new profile established

The winning channel build was instrumented inside the actual selected semantic
terminal, not an isolated substitute. The representative maximum-body withdrawal
rollover reports these intervals, including checkpoint overhead:

| Interval | CU |
|---|---:|
| Public validation, openings, selectors | 18,214 |
| Projected Poseidon | 58,856 |
| Other semantic constraints | 58,679 |
| Copy terminal | **116,400** |
| Composition blend | 5,187 |
| Remaining terminal/equality/masking | 13,134 |

Selectors were already shared between semantic and copy evaluation: no saving
was booked for sharing that already-shared work. The preceding inactive
six/seven-product field control was not rerun. The new tag bound targets an
actually executed function, `copy_tag_coordinate_dot`.

## Exact rewrites and proof scope

### One suffix chain, fourteen copy patterns

For arbitrary openings, set `S16=0` and `Sj=lambda*(xj+S(j+1))`.
A window of length `n` starting at `j` is
`Sj - lambda^n*S(j+n)`. This simultaneously supplies the source's overlapping
six/eight/sixteen-column patterns. Small patterns and the public offset are
retained exactly; no division or nonzero-lambda premise appears.

[CopySuffix.lean](experiments/CopySuffix.lean) proves the append/split identity
symbolically and proves equality of **all fourteen** source-shaped pattern
expressions over any commutative ring. It covers arbitrary, not just honest,
openings, zero/one challenges and the public offset as an arbitrary scalar.
Only the fixed sixteen-cell layout is expanded in the final small proof.

The actual source overlay, [copy-suffix.patch](experiments/copy-suffix.patch),
is selected only by `v8_copy_suffix`. It is compared against both the original
windowed evaluator and the independent source literal-pattern evaluator on
2,560 arbitrary/degenerate cases. The selected copy-lane host-reference tests
also pass. These are actual Rust tests, not tests of a separately copied fast
function. The source's typed-registry equality test checks the frozen patterns.

### Seven products are safe for these tags; eight are not

The frozen tags are at most `1,124,073,607`, substantially below `p-1`.
For canonical selector limbs:

```
7*(p-1)*1,124,073,607 = 16,897,507,815,529,117,854 < 2^64
8*(p-1)*1,124,073,607 = 19,311,437,503,461,848,976 > 2^64.
```

[CopyTagRange.lean](experiments/CopyTagRange.lean) proves the product bound,
every partial accumulator's range, the exact margin, and modular equivalence
of changing adjacent batch boundaries. [copy-tag7.patch](experiments/copy-tag7.patch)
adds a **compile-time assertion over every actual tag** and changes the raw
accumulation width from four to seven, only under `v8_copy_tag7`.

All terms still contribute. Across the thirty actual tag coordinates the
source count changes from **85 to 52 chunks**: 132 fewer limb reductions and
132 fewer reduced-limb additions, with the same 272 tag terms. No claim that
an honest residual is zero is used. The changed source passes 15,360 literal
coordinate comparisons, including all-max canonical selectors, with optimized
checked arithmetic, plus the dependent copy-lane tests.

Both Lean leaves replay without `sorry` or new axioms. Their scope is
kernel-checked algebraic/list/range equivalence, not Aeneas translation of
Rust, its parser, compiler or whole verifier. Canonical selector limbs follow
the existing checked field construction; malformed inputs do not gain an
alternate parser. Actual-source differentials and full-transaction tests are
the present source correspondence evidence, not a claimed universal translated
`Verify_fast = Verify_reference` endpoint.

## Tests, resources and retained limitations

The final build has 24 maximum-body and 24 ordinary-body cases, including wrong
release, altered proof, stale lane and replay controls. Two additional cases
reach the real verifier then fail Token CPI and preserve protected accounts
byte-for-byte. Rollover stale-lane/replay cases not implemented by the existing
driver are not counted. The suffix-only intermediate matrix has 24 cases.
No witness/secret bytes or new fixture binaries are committed.

Focused Lean leaves used the clean, pinned Mathlib cache on the local Mac;
NUC optimized Rust/SBF builds ran in 5/7-GiB High/Max scopes, SVM in 3/4-GiB
scopes, all with `MemorySwapMax=0`. Times, RSS, exits, source/ELF hashes and
axiom logs are in [copy-performance-evidence.json](copy-performance-evidence.json).
The direct-r10-offset audit reports 4,096 bytes; it is not a full machine
pointer/call-stack proof. No new SBF stack warning appeared.

One Lean preflight used the wrong direction of `Nat.add_mod`; one Rust test
needed `std::println!` in the no-std crate. Their failed logs are retained,
followed by focused corrected replays. There was no memory-cap increase or
weakened arithmetic. The first suffix preflight used obsolete Matrix lemma
names; replacing them with definitional reduction fixed it (exit 1, 15.91 s,
2,900,459,520-byte RSS, zero swap; diagnostic captured in the tool transcript).

No new proving-time/RSS measurement is claimed: the same archived proofs are
accepted. These internal equalities leave the proof view and challenge framing
unchanged, but do not close the inherited full-view simulation, global recovery
or resource-bounded Fiat–Shamir obligations. Grinding credit remains zero.

## Reproduce and next decision

On the pinned task-owned NUC copy, after the documented channel/Pool overlays:

```
bash experiments/run_copy_suffix_nuc.sh prepare NEW.log
bash experiments/run_copy_suffix_nuc.sh test NEW.log
bash experiments/run_complete_build_nuc.sh suffix NEW.log
bash experiments/run_copy_suffix_nuc.sh prepare-tag7 NEW.log
bash experiments/run_copy_suffix_nuc.sh test-tag7 NEW.log
bash experiments/run_complete_build_nuc.sh tag7 NEW.log
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
  ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
  ASPIS_TOKEN_ELF_DIR=<pinned LiteSVM elf directory> \
  bash experiments/run_complete_matrix_nuc.sh tag7 NEW_DIRECTORY
```

Here `experiments/` abbreviates this directory's experiments path. Preparers
fail closed on an unknown source hash; do not reset a worktree to satisfy them.
`terminal-profile.patch` plus `channel-profile` is a diagnostic-only build;
the quiet winners do not include the checkpoint calls. The no-std test fix is
already in the final seven-tag patch; its separate fix patch records the failed
preflight and is not needed for fresh preparation.

Locally, run `lake env lean -M7000 <absolute changed leaf>` from the pinned
`AspisFormal` workspace and `python3 experiments/audit_copy_performance.py` to
recompute the machine-readable measured comparison from archived JSON.

**Keep both wins.** The next decisive optimisation experiment is a frozen,
aggregated copy-selector plan replacing the remaining 136-link runtime scatter:
derive it from the actual table, prove finite-sum regrouping, compare all public
weight branches and arbitrary openings, then measure the same complete proofs.
Reject it if it regresses the quiet SBF build. This is a bounded next target,
not a claim that all optimisation opportunities have been exhausted.
