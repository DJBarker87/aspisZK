# R68: concrete traversal models and generated caller integration

Base revision: `b99b3220a41429afb4cef6bf033c4ff9584ccf32`.
Selected runtime and proof fixtures unchanged. This milestone does **not** close
the Rust library/source-refinement, circle execution, privacy or soundness gate.

## What compiled and was proved

Five focused Lean targets compile against the pinned full Aeneas runtime and
R66 cache. There are 25 new proved theorems, plus three dependency/axioms audits
of generated function definitions. No new axioms, `sorry`, or external templates
are accepted. Standard dependencies are at most `propext`, `Classical.choice`,
and `Quot.sound`; exact per-declaration results are in the logs and receipt.

- `TraversalRuntime`: explicit state-threading array traversal, chain state,
  chain construction/next, next-based `any`, slice `any`, and `Option.ok_or`.
  Proves that a successful array traversal preserves length. Failure and
  divergence are retained rather than assumed absent.
- `TraversalLaws`: 20 theorems covering append composition, callback order and
  state, four-element and empty arrays, first failure/divergence, `any` stop/
  hit/continue/failure behavior, chain left exhaustion and an unfused right
  iterator, and option success/error conversion. The stateful-map positive and
  stale-state negative controls are proved, not sampled.
- `AspisR68Circle.Types` / `Funs`: the complete R67 **eta-normalized diagnostic**
  generated declaration bodies, with only namespace and import changes, now
  elaborate with these concrete models. The preflight checks the bodies exactly.
  These are modeled integration artifacts, not an accepted Rust source theorem.
- `TraversalCaller`: four theorems identify the two generated conversion
  callbacks and prove their four-element array results in this model. Three
  further `#print axioms` commands inspect the complete guarded-product and
  circle/secure-OOD definition closures. Auditing a definition does not prove
  its intended arithmetic specification.

## Exact final replay

NUC cache: `/home/dombarker/project-offloads/aspis-r66-final-20260929-a`.
Output: `/home/dombarker/project-offloads/aspis-r68-final-20260929-a`.
Lean `leanprover/lean4:v4.32.0`; `lake env lean -j1 -M4500` per leaf.
Kernel scope: MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0, TasksMax 128.
310 retained targets reused; five compiled; 203 dependency source/object pins.

| Target | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| TraversalRuntime | 0 | 1.34 | 2,535,700 | 0 |
| TraversalLaws | 0 | 1.72 | 2,531,040 | 0 |
| AspisR68Circle/Types | 0 | 1.17 | 2,529,356 | 0 |
| AspisR68Circle/Funs | 0 | 2.10 | 2,581,376 | 0 |
| TraversalCaller | 0 | 1.16 | 2,521,064 | 0 |

Evidence: [receipt](evidence/r68-traversal-library/receipt.json),
[final logs and metadata](evidence/r68-traversal-library/final/metadata.json),
[content manifest](evidence/r68-traversal-library/MANIFEST.json).
Run `python3 tools/check_r68_library.py` from this research directory.
R67's obstruction evidence checker also still passes, with its source gate OPEN.

Focused failures are retained: early map proofs needed explicit Result case
analysis and dependent-array elimination; extra `rfl` steps after solved goals
were removed. The generated integration needed explicit cached discriminant,
wrapping-arithmetic, array/slice and Result-conversion imports. Attempt `e`
stopped in dependency preflight because the broad `Aeneas.olean` umbrella was
not cached; it did not start a cold dependency build. A module documentation
command before imports was corrected to a plain comment. Failed logs are not
counted as theorem evidence. The single final replay above followed the passing
focused leaves and caller check; no unchanged runtime/SBF suite was rerun.

## First remaining source-specific proposition

For the selected `r24_canonical_mul` call site, establish that the real Rust
`Chain<slice::Iter<u32>, slice::Iter<u32>>::any` over the two four-limb arrays,
with predicate `limb >= P`, has the same result, callback order and retained
iterator state as the concrete model. The actual generic `Iterator::any` calls
`try_fold`; `Chain` overrides `try_fold`. A theorem about a next-based loop alone
does **not** justify replacing every possible iterator implementation.

Similarly connect the concrete `array.map` source path (including its
`try_map`/drain machinery) for these Copy scalar callbacks to the ordered model,
and justify the two `.map(u64::from)` to eta-closure normalization sites, or fix
the pure-function-item lowering in the pinned translator. The new `map_eta`
theorem is only Lean function eta equality; it is not that Rust normalization
theorem. Pointer validity, unsafe library internals, destruction/unwinding and
compiler correctness are not proved by this milestone.

After that source boundary: prove generated guarded QM31 multiplication using
the retained R56/R59 width/residue bounds, compose the already-proved R66 inverse
with the complete circle map, retain singularity-before-subfield error order,
then handle the bounded sampler observer. Do not replace any of these steps
with an assumption of correct multiplication or independent uniform challenges.

## Unchanged release boundary

No production code, profile, proof format, negative regression or hiding
assumption changed. No new CU measurement: the selected endpoint remains
**1,497,377 / 1,498,764 CU**; both actual 1M-cap executions still exhaust.
Shared-oracle/seed/commitment laws, the complete causal public view, visible
failures/retries/publication and numerical loss composition remain open.
Coherent pre-beta quotient-pair extraction remains a separate soundness gate.
The persistent full-repair/full-privacy goal is not complete.
