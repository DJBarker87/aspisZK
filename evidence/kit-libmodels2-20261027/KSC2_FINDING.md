# Library-model fidelity audit, second half

Stage 1: scope frozen; verdicts pending focused validation.
No premise removed; headline `AspisR1.RPx_Deployed.deployed`, frozen3,
narrowed D188 and the owner-approved trust inventory are unchanged.

The literal `counterpart == "library model"` selection has 184 rows. Stable
alphabetical sorting by the inventory declaration `name` assigns rows 92–183
(zero-based) here: `Iterator.any.default` through `validChunk`. The input
contains non-library aliases/adapters misclassified as library models; these
remain explicit rather than receiving std fidelity credit. The exact split,
source hashes and genuine std/core cross-check are in `KSC2_assignment.json`.

Only KSC2_ modules and this evidence directory may change. Budgets: 80 Lean,
10 optimized Rust, zero Kani; one capped host scope at a time. Existing SInt2
and KSA objects will be reused read-only; new objects use the required
persistent cache. No shipped source or artifact changes are authorized here.

## Per-model results

Pending. Complete inventory rows will retain UNDETERMINED where no universal
association or valid Rust-library counterpart is available.

## Stage 2: focused evidence

`KSC2_P7` proves eight constructor/collection wrappers equal to the exact
Aeneas constants selected by LEAN_PATH. `KSC2_Simple` proves Option/Result
branch semantics, lazy map construction, Windows creation/content/next laws,
and shared `next_back` branches. `KSC2_MutCounterexamples` proves the crossed
mutable cursor counterexample and the unchanged slices returned by the
mutation-blind `any`/`all` interfaces. Every accepted root prints only standard
axioms. L001 is retained as a failed discovery of two absent P7 constants;
L004 is rejected for missing FnOnce parent fields. Neither is accepted evidence.

R002 runs five optimized std-only test groups on Rust 1.94.1/e408947bf,
including mutation, mixed front/back iteration, empty and early-stop branches,
state threading, expected panics and cross-split array/conversion controls.
R001 is a rejected test-compilation error: TryFromSliceError has no PartialEq;
R002 unwraps only the expected-success conversion cases. The entire frozen
release Cargo manifest graph is validated offline against a byte-identical
scratch lock before each run; the tests themselves use optimized rustc --test
and link only std. This is not a shipped-source rebuild or native release
profile claim. Both post-run lock hashes are unchanged. No Kani or ELF ran.

The online versioned rustdoc URLs were unavailable through the web tool.
`KSC2_rustdoc.json` therefore hashes and excerpts the host's installed 1.94.1
rustdoc pages; every page contains the pinned version. This supplies exact
versioned documentation rather than silently substituting today's web docs.
