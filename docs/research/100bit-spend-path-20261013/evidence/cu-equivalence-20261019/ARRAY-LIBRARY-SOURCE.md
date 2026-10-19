The complete fixed-prefix kernel/query comparison is checked under an
explicit concrete array-builder interpretation, not an admitted opaque
from_fn axiom. Its Rust standard-library source admission remains OPEN.

Pinned Rust: nightly-2026-06-01. Exact source files, compiler version, LLBC
hashes and all eight diagnostic receipts are in array-library-diagnostic-a.
The collector copies only a byte-exact excerpt of the 43958827-byte trace;
the complete trace remains on the NUC at the hashed manifest path. No binary,
full trace, failed axiom template or partial Lean emission is promoted.

Built-MIR extraction with actual array::from_fn, try_from_fn,
try_from_fn_erased, Guard.push_unchecked and NeverShortCircuit source succeeds
(cu-dots-charon-array-a, exit0, wall1.804s, RSS239784KiB). Strict Aeneas fails
at generic Try::from_output (try_trait.rs:192). The trace identifies actual
argument [TraitClause0::Output; N] versus expected
TraitClause1::ImpliedClause0::Output. This is an associated-type normalization
boundary; no arithmetic or whole-kernel inequality is implied. Initial
reference to branch was refined by the trace to from_output.

Continuing strict per-function translation, with failures still recorded,
identifies two further independently failing source bodies:
try_from_fn_erased at array/mod.rs:912 and Guard.push_unchecked at line954,
both reporting Can't copy a mutable borrow. The emitted partial files also
expose the current Try/Residual trait-family incompatibility: Rust Try has an
associated Residual bound implying Residual<Self::Output>, while the pinned
backend dictionary represents only the FromResidual parent. Mutually recursive
Try/Residual dictionaries are not supported by this backend. None of these
partial definitions is admitted or imported by the checked kernel proof.

Supported compiler monomorphization was tested without changing Rust bodies
(cu-dots-charon-array-mono-a, exit0, wall1.805s, RSS243272KiB). It resolves
concrete generic selection but erases the Guard field's reference lifetime;
strict Aeneas rejects RErased in TypesAnalysis.ml:229. This route cannot be
adopted by inventing lifetimes or weakening the borrow checks.

Elaborated MIR was tested to isolate built-MIR scaffolding. Extraction
succeeds (wall1.805s, RSS239368KiB), but the same generic type and mutable-copy
failures remain, with additional outer-loop reconstruction limitations.
Changing MIR phase is therefore not the repair. All diagnostic runs use
actual memory high/max6/8GiB, swapmax0 and zero process/cgroup swap. Exact
commands, revisions, features, exits, wall times and RSS are in the receipts;
#print axioms is inapplicable to frontend failures, not silently successful.

The pinned Charon source identified the subsequent investigation:
charon/src/bin/charon-driver/translate/translate_bodies.rs:970-975 translates
MIR CopyForDeref as Use(Operand::Copy(place), WithRetag::No). That may explain
the rejected projected mutable-reference operations. Next isolate a small
projected mutable-slice length/reborrow example, with direct/shared-reference
controls, before implementing a source-checked normalization of dereference
scaffolding. The ordinary mutable-copy rejection must remain enabled, and
source place identity/liveness must be established before eliminating any
temporary. This isolated investigation has now been completed as described
below. Independent generic Try/Residual dictionary/normalization support
is still required. Charon's partial specialization machinery preserves region
parameters; full monomorphization does not, so any specialization experiment
must retain and check the required lifetime correspondence.

No compiler check, Rust statement or theorem statement was weakened. The
remaining library/helper/enclosing-verifier bindings and final whole-program
soundness/privacy transfers remain obligations. This diagnostic frontier is
not a completion claim or a reason to mark the full goal blocked.

The four-function diagnostic in `tools/cu-equivalence-20261019/deref-repro-input`
uses a projected mutable slice, an explicit reborrow, a direct mutable slice
and a shared-reference control. Built MIR emits all four successfully.
Optimized MIR fails exactly the projected and explicit cases with the same
mutable-copy error as the library. The emitted LLBC exposes an anonymous
mutable-slice snapshot followed immediately by a reborrow of its dereference
and metadata. The direct/shared controls continue to translate. This refines
the earlier suspected CopyForDeref connection into a reproducible MIR-phase
diagnostic; it does not prove the provenance of every LLBC copy.

`normalize-deref-temporaries.py` is an EXPERIMENTAL LLBC rewrite, not an
admitted compiler pass or a theorem. Its syntactic guards require an anonymous
nonargument temporary, identical mutable-slice types modulo regions, no
self-dependent source, no intervening semantic statement or protected storage
change, exactly one matching reborrow of the temporary and its metadata, and
no other use anywhere in the function. It substitutes the original place in
both positions and removes the snapshot assignment. Ordinary mutable-copy
checks remain enabled. Rust source/signatures remain unchanged; two LLBC
bodies ARE rewritten. A source place/alias/retag semantic justification is
still needed before this pass can be admitted into the proof pipeline.

The positive diagnostic runs with Aeneas `-checks` and produces Types/Funs
byte-identical to the successful built-MIR emission. Four explicitly synthetic
negative inputs test an extra snapshot use, a named local, an intervening
write and a protected StorageDead. Each leaves the unsupported copy in place
and Aeneas rejects it; the other function remains eligible. Synthetic inputs
are not claimed to be compiler-produced or borrow-checker-valid Rust. The
five-case capped run and each case have command/revision/features/exit/wall/
RSS/swap receipts. `check-deref-evidence.py` rechecks these artifacts and the
normalization witnesses without rerunning the frontend or Lean.

Applied to the actual pinned library LLBC, the guarded rewrite selects two
sites: try_from_fn_erased's shared reborrow and Guard.push_unchecked's
TwoPhaseMut reborrow. The extensive-checks whole-library emission still exits
1: the generic Try::from_output type mismatch remains, and the loop now reaches
`Could not compute a loop fixed point in 2 iterations`. The two mutable-copy
errors are absent. Config.ml describes this iteration bound as a sanity/bug
detector, so it has not been silently raised. Exact attempts:
`array-deref-normalize-a`, `array-deref-normalized-aeneas-a`.

The Guard type and successful push_unchecked declaration have been selected
byte-for-byte, excluding all failed declarations and generated axiom templates.
`emit-array-guard.py --check` verifies those cuts. The promoted namespace
AspisR1CuArraySource uses explicit Option-based MaybeUninit and safe-domain
index/write/add interpretations. Those definitions introduce no equivalence
axiom and have NOT been claimed admitted to the Rust unsafe primitives.

`CuSavingsArrayGuard.source_success` checks the entire selected emitted write
operation under that interpretation: an in-bounds initialized index implies
successful indexing, no-overflow increment, exact requested cell replacement,
and exact mutable handback. Its frame/written theorems cover every other cell
and the target cell. `CuSavingsArrayGuardPrefix.push_prefix` consumes the
execution theorem to extend the initialized-prefix invariant by precisely the
new item, preserving buffer length. This is the step needed by the enclosing
array initialization loop, not a replacement axiom about that loop.

Five new focused targets passed, with standard Lean axioms only: guard types,
primitives, emitted push, its execution proof and the consuming prefix proof.
Receipts are `cu-array-guard-types-a`, `cu-array-guard-primitives-a`,
`cu-array-guard-push-a`, `cu-array-guard-proof-c`, `cu-array-guard-prefix-b`.
They use 1.60–1.81 seconds, peak below 2.6 GiB RSS and zero process/cgroup swap;
every result includes #print axioms. Earlier local theorem errors are retained
as failed attempts, with no release claim.

Next: justify or replace the experimental frontend rewrite, resolve the actual
library loop and Try/Residual dictionary translation, and admit the concrete
unsafe primitive interpretation. The full library, shared arithmetic helpers,
enclosing verifier and final soundness/privacy transfers remain OPEN.

The loop's fixed-point diagnostic has subsequently been isolated and repaired
in a separate opt-in frontend. `match_types` had no case for two identical
region-free associated-type projections. The narrow added equality case lets
the exact normalized library loop pass strict symbolic borrow-checking with
the unchanged two-iteration limit. All 14 paired compatibility controls pass;
the full library emission now fails only at the Try/Residual typing/dictionary
boundary. See ASSOCIATED-TYPE-MATCHER.md for scope, hashes, exact receipts and
the distinction between borrow-checking and Lean/source admission. No new
Lean target or whole-library completion is claimed for this frontend repair.
