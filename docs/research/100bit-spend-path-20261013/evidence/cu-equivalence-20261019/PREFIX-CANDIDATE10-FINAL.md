# Candidate 10: fixed 608-byte prefix equivalence complete

Candidate `225a3736d8afb8e8d77b38f1b62edbc7f227b5fe`, exact parent
`8cdeaf7167a9dd1a1d6745c0765ab5fd0aa4af88`; frozen production
`39c2971dd16c95858a4cfd2c9ae35da052eacfa9`. Retained measured saving:
**12,364 combined CU**. These are existing runtime measurements; no production
Rust, ELF, protocol, proof bytes, checkpoint or transcript was changed here.

`CuSavingsPrefixCandidate10.helper_equivalence` compares the complete exact
old/new four_dots helper on every slice of length at least 608. The source
kernel comparison preserves arbitrary shared arithmetic computations, checked
index/conversion failures, unwrap panic and divergence. It does not assume
successful decoding, valid fixtures, canonical field operands, or an
arithmetic/optimization equivalence law. The nine Arithmetic operations are
identical original source callees with shared types on both sides; their
complete field/wide/dot source files are pinned byte-identical in the exact
parent, candidate and frozen production. This parametric comparison applies
to those unchanged operations without proving their arithmetic again.

The former std builder gap is closed explicitly. `sourceOld` and `sourceNew`
use the actual emitted original `AspisR1CuArrayGraph.core.array.from_fn`.
`old_library_admission` and `new_library_admission` consume the already checked
`CuSavingsArrayFromFn.source_eq_build`, including the actual mutable source
callback bodies and source builder state handback. No arbitrary-map or
arbitrary-array-constructor law is assumed.

`caller_context` consumes actual `View.query` execution and derives the 608-byte
bound from `CuSavingsQueryAccess.query_prefix_bound`, for arbitrary View/index
inputs. Query failure/divergence is preserved. The universally quantified
unchanged context may hash, reject early, emit traces, mutate state and consume
the dot result; the complete original query slice remains available. This
covers the sole production helper call in query_with_geometry. The source
checker inversely factors the complete parent/candidate caller, and separately
the frozen caller (whose later rho continuation differs). Both bind the same
actual query and dot helper once; no success or source-equality premise is
introduced by that factoring. The query source kit pins the complete View
carrier, actual query body, folds and salted widths for the measured
`pool-adapter,private-leaf-salts` feature boundary.

All **44 selected targets** pass with coherent source/object/direct-import
hashes. The final focused receipt `prefix-candidate10-qualified-a` records exit
0, wall **1.604 seconds**, peak RSS **2,584,228 KiB**, zero process/cgroup swap,
exact command/revision/features and four `#print axioms` results. The complete
selected closure peaks at **2,679,312 KiB**, with zero swap. Only standard Lean
axioms and inherited `core.fmt.Formatter : Type` occur; Formatter is the existing
opaque backend type referenced by unwrap Debug dictionaries, not an
optimization-equivalence proposition. The unchanged dependencies were reused.

Unified imports exposed a generated global Variant discriminator registration
collision. `emit-cu-query.py` now inversely audits a source-preserving qualified
registration with the same three constructors and 0/1/2 ordinals. Query Funs is
byte-unchanged. Only its six affected targets were refreshed; no theorem
statement or Rust body changed.

The result uses the inherited Rust→Charon→Aeneas compiler/runtime admission.
It is an original-source helper proof plus inverse-audited caller-context
composition, not a new proof of the compiler or extraction of the entire
transaction. The selected run DAG, exact source spans, helper/caller binding,
complete generated declaration re-pin inventory and hashes are recorded in
`PREFIX-CANDIDATE10-FINAL.json`. `check-prefix-candidate10.py --check` verifies
them without compiling or rerunning runtime gates.

An unneeded diagnostic attempt to extract the unchanged raw multiplication
hit Aeneas's unsupported function-item callback type. A source-local eta adapter
then emitted successfully. Neither diagnostic emission nor an adapter theorem
is imported/admitted into this proof: universal identical-callee substitution
makes that arithmetic extraction unnecessary. Its run receipts are retained;
no failed frontend run is selected as proof evidence.
