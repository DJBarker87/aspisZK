> Historical finding retained from 7e46a8b2c9. The D362 resume does not retract this generic obstruction or call it a privacy counterexample. Current finite-type/world-indexed source packages and their boundaries are recorded in REPORT.md and AUDIT.md.

# V170: generic fixed-callback projection obstruction

Target not yet established. No recount row or endpoint premise is discharged.

The requested V184-style installation must not silently conflate a pure value
projection with complete native Result/world correspondence. The actual candidate
signature is `ExternalFuns.op4 {T : Type} : T → Result Unit`; it receives neither
a Drop dictionary nor a world. `op4-signature.json` records its exact tracked
source, blob and SHA-256. The row is generic in T, rather than a statement that
only a specifically identified Drop-free type is consumed.

The tested uniform statement is:

> There exists one fixed callback `Input → Result Unit` whose complete Result
> agrees with native `core::mem::drop(Input)` in every initial external world.

For this statement, the input is one inhabited zero-sized Rust type. Its Drop
implementation increments an external counter, reads an external AtomicBool,
and panics exactly when that flag is true. It contains no flag in its value.
The same input value in the false-flag world returns; in the true-flag world it
panics. Each execution enters its destructor exactly once. Regardless of whether
an effect interpreter classifies panic as failure or nonreturn, the two complete
outcomes differ. A single pure callback applied to that same input cannot equal
both outcomes.

`PV_FXM_DropCounterexample.no_world_free_callback` proves the contradiction for
**any** result type and any pair of distinct outcomes. `.no_uniform_projection`
instantiates it on the one-value input carrier; `.witness` distinguishes the two
observations; `.state_indexed_nonvacuous` constructs a state-indexed callback.
These are logical theorems, not extraction/refinement of a destructor.

## Checked native and source evidence

`drop-counterexample-02/output.log` records **32 paired finite-validation cases**
on nightly-2026-06-01, rustc 1.98.0-nightly (14210df0e, LLVM 22.1.6), optimized
with `-O -C panic=unwind`. The native calls use real `core::mem::drop`; the owned
wrapper calls the same library function. Normal return/panic and exactly one
destructor entry agree for both flag values in all pairs. This tests the finite
witness and the wrapper, not an unbounded compiler or memory-model refinement.

`PREFLIGHT.json` script-checks the complete pinned stdlib drop definition and
records its file SHA-256. Its empty lexical body still has an owned parameter
requiring automatic Drop glue on exit. The source check is **not** a structural
closure gate for generic Drop glue, an allocator law, or a deployed-path proof.
It also verifies the 601 Init objects used by the Lean module against the h4
manifest before compilation, and finds no prior uses of IDs 35500–35599 in the
shared sent file or the scanned Stream B run/receipt/evidence directories.

The first native wrapper attempt failed before rustc started because rustc was
absent from the scope PATH. The changed second driver uses the absolute pinned
compiler path. SSH failures and read-only receipt recovery are retained; no
submitted compiler was rerun unchanged because receipt collection failed.

## Scope and consequences

This is a counterexample to the **fixed, world-independent, generic full-Result
projection**, not a counterexample to Rust drop itself, a claim that this custom
destructor occurs in the shipped prover, or a counterexample to a world-indexed
family of dictionaries. It does not refute an independently specified effect-aware
interpreter. The external flag belongs to the destructor's accessible world;
it cannot be assumed to be a disjoint frame to remove the discrepancy.

A fixed callback cannot be repaired merely by adding allocation counters/history,
buffer identity, capacity, data memory, or an arbitrary frame to a separate
observation if its projected Result is still required to equal that one callback
in both worlds. Neither returning `ok ()` unconditionally nor assuming away
panicking destructors closes the original generic statement.

A repair needs an explicit world-indexed interpretation, with consumed execution
composition proved, or a proved restriction on the actual consumed types and
destructors. Neither repair is claimed here. No original carrier, trust field,
observer, simulator or deployed theorem has been changed. In particular, the
counterexample does not establish that every possible formulation of V170 is
false; it prevents reporting the tested uniform formulation as row closure.

Under the requested checked-counterexample stop condition, retain all four rows:

| Row | Disposition |
|---|---|
| V170 / op4 drop | OPEN; fixed generic full-Result projection refuted by the finite native witness plus the logical impossibility theorem |
| V183 / op32 try_reserve_exact | OPEN; no complete allocator/error/capacity law or installation attempted after the finding |
| V221 / op122 array zeroize | OPEN; no volatile-write/iterator-restoration/fence law or installation supplied |
| V222 / op123 blanket zeroize | OPEN; no default/volatile-write/fence law or installation supplied |

No combined row audit or closure replay is claimed: no complete row was obtained.
The logical counterexample has its own focused compile and five axioms queries.
Zeroize source/compiler non-elision and the separate L3 binary question remain
unchanged obligations. No finite test is promoted to a binary erasure guarantee.
