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

The pinned Charon source gives a concrete next investigation:
charon/src/bin/charon-driver/translate/translate_bodies.rs:970-975 translates
MIR CopyForDeref as Use(Operand::Copy(place), WithRetag::No). That may explain
the rejected projected mutable-reference operations. Next isolate a small
projected mutable-slice length/reborrow example, with direct/shared-reference
controls, before implementing a source-checked normalization of dereference
scaffolding. The ordinary mutable-copy rejection must remain enabled, and
source place identity/liveness must be established before eliminating any
temporary. Independent generic Try/Residual dictionary/normalization support
is still required. Charon's partial specialization machinery preserves region
parameters; full monomorphization does not, so any specialization experiment
must retain and check the required lifetime correspondence.

No compiler check, Rust statement or theorem statement was weakened. The
remaining library/helper/enclosing-verifier bindings and final whole-program
soundness/privacy transfers remain obligations. This diagnostic frontier is
not a completion claim or a reason to mark the full goal blocked.
