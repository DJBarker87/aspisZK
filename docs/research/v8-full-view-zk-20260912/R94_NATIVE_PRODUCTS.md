# R92–R94: streamed sparse contraction and rejected product schedules

2026-09-30; base `4b772362569f2c527dfe4b79f1cb93753982aaa8`.
Research only. Neither under-1M execution nor full security is achieved.

| Complete verifier | World 0 CU | World 1 CU | Decision |
|---|---:|---:|---|
| Pushed R91 control | 1,135,747 | 1,134,007 | Retained |
| R92 streamed sparse G | 1,131,836 | 1,130,098 | Compose |
| R93 outlined mixed opening limb | **1,130,010** | **1,128,272** | Selected research candidate |
| R94 twelve-product arithmetic | 1,273,103 | 1,271,360 | Reject regression |
| R94 bounded wrapping pair products | 1,164,618 | 1,162,875 | Reject regression |

These are complete executions of the same two R84 proofs, not new fixtures,
kernel estimates or settlement transactions. Both actual 1M honest runs still
exhaust. The remaining gap is **130,010 CU** on the larger fixture. All corrupted
combined finals reject with Custom(6), without resource failure, at both caps.
Heap stays 262,144 bytes and simulated accounts are unchanged. No validation,
query, challenge, digest width or profile change is selected here.

## Selected changes

R92 streams the sparse G contraction through the existing private canonical
arithmetic instead of gathering pairs into temporary arrays. Each low group
accumulates its normal/carry products directly, then joins the scalar dot.
The retained old kernel and independent full-chord calculation remain as
differential checks. The internal accumulator has a 4,096-term bound and keeps
partial representatives below the stated u64 limit; canonical input conversion
remains. This is an internal canonical-workspace contract, not an assertion
about arbitrary malformed internal arrays.

R93 outlines each complete mixed-width opening limb. It does not inline the
generic field multiplier, change the 38-term arithmetic, or skip zero-weight
inputs. Its 1,826-CU saving on each proof is a measured call-layout effect.
The unchanged ordinary checker is reused with exact source and log pins.

Both selected stages pass source checks, both honest host audits, 3,282 wire
cases (3,281 checked rejections), the SBF frame/table gates and complete runtime.
The selected manifest is
`94133394e2f68a0f1b59e6b2853945ce2b9356dfc03c343dc50074276d80a20f`;
ELF `0e175a42b6c91873ab85af136802bb58f5b1fa51ca7d48940f74ef792fa7e00d`.

## Why the arithmetic candidate is rejected

R94 replaces four complex cross-products with unreduced pair-product identities,
reducing the logical integer products from sixteen to twelve. It passes
262,144 product cases, including all 65,536 selected boundary combinations,
against frozen source and an independent i128 extension-field formula. Pair
products and subtractions are also checked as integers; private dots cover
lengths through 4,096. Source, malformed-input and runtime gates pass.

Nevertheless, the first complete build is much slower. Its exact execution
trace assigns **92,966 exclusive instructions** to `__multi3`. Explicit bounded
wrapping multiplication removes this helper from the leading costs: canonical
pair sums satisfy `4(P-1)^2 < 2^64`. No global overflow setting or raw-input
fallback is removed. That variant still regresses by **32,782 / 32,777 CU**
against its actual R92 control, so neither R94 variant is composed.

| Executed world-0 instructions | R93 selected | R94 first | R94 bounded |
|---|---:|---:|---:|
| Total | 1,019,898 | 1,162,551 | 1,054,286 |
| Integer multiply | 65,663 | 65,869 | 55,319 |
| Loads | 196,836 | 217,782 | 211,693 |
| Stores | 121,812 | 145,199 | 139,281 |

These are exclusive instruction counts, not disjoint inclusive CU budgets.
All traces match their exact ELF text and clean complete-execution CU. The
trace driver's inherited `--micro`/scope label selects a single honest run;
it does not substitute a kernel ELF. Budget claims use the separate full
four-row runtime receipts, never that label or a high-cap run alone.

## Evidence and open security boundary

`python3 docs/research/v8-full-view-zk-20260912/tools/check_r94_evidence.py`
checks the parent evidence, source deltas, complete runtime, malformed controls,
stack gates, traces, exact pins and resource logs. Raw register dumps, proof
fixtures, ELFs and keys are not collected. NUC caps remain host 5/7 GiB,
SBF 12/16 GiB, runtime 2/3 GiB, collection 1/2 GiB, with MemorySwapMax=0;
all retained process swap counts are zero. The Solana skill's complete-source,
malformed-input, stack and runtime gates govern selection.

No new Lean targets in this checkpoint. R91's extracted query-loop value/state
theorem is retained; its public guard and complete observed shared-oracle
history remain open. The first profile proposition is still universal
actual-source C1/H1/G joint affine-image compatibility for R84, including p0/p2,
adaptive/degenerate prefixes and justified exception losses. Finite rank
certificates are not this theorem. Causal posterior simulation, seed/commitment
composition, retry/publication, coherent pre-beta quotient-pair extraction and
full soundness remain open. R84 is not security-promoted; all negatives remain.
No deployment, wallet operation or production-path change.
