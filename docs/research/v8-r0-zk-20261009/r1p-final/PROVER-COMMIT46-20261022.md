# Prover commitment continuation 46

Target not yet established. Base 4a7c0512e (LOG D158), branch
`codex/cx-prover-commit46-20261022`. Work proceeds under D158's explicit
state-passing interpretation of ProgramOne; no interior-mutability trust law
is authorized or introduced. D143 observables, the D146 statement domain,
and adversarial environment/public nonce remain the intended contract.

## Stage 1: ProgramOne state transition

The retained native harness copies the shipped `ProgramOne` and concat bodies
verbatim. BTreeMap insertion is substituted by the existing D133 per-key
contract: arbitrary prior value, exact replacement, and an untouched frame.
The Kani comparison checks the digest, complete represented map update,
sticky collision flag, and a fresh mutable borrow after return. This does not
verify B-tree internals or arbitrary address lengths; the independent Lean
map/concat interface is responsible for those universal parts.

The owned reference has an explicit `ProgramState { table, collision }`
argument and returns the digest and updated state. It retains repeated writes
and unequal old-value collisions. No shipped file has been edited.

## Remaining stages

Complete publication, source-to-FSExperiments conversion, shippedProverExperiment,
both WholeRunJoins, and deployed endpoint premise removal remain pending.
No release/privacy closure claim is made by this checkpoint.

`ProverCommitProgramOne46.call_exact` proves the extracted state-passing
operation returns exactly the updated table and collision flag for every
map state, answer and parts value. `reference_decode` / `call_decode` use
only the existing insert-state and insert-previous TrustedStd fields;
`continuation_exact` reuses the part-28 generic monadic install theorem.
`ProverCommitProgramLog46.run_exact`, `expected_decode` and
`publication_consumer` thread the complete ordered log through publication,
including duplicates and the final flag. `append` composes tree logs without
resetting state; `sticky` retains every earlier collision. These are caller
transports, not a claim that codecs or multiproof generation have been joined.

Native per-call Kani passes (14.795 s, 1,608,816 KiB peak RSS, zero swap).
The first launch was rejected by the Kani CLI before compilation for a missing
unstable-options switch; v2 corrects the command. Charon and Aeneas translation
of the owned reference pass, and the two generated modules compile at
J9637–9638. J9641 and J9643 accept all eleven new bridge/log theorems; their
axioms are subsets of [propext, Classical.choice, Quot.sound]. J9639, J9640
and J9642 are rejected proof drafts, retained as failures, never accepted
as evidence. Full section-6 fields, source hashes, dependency fingerprints,
commands and axiom lines are in `../../100bit-spend-path-20261013/evidence/
prover-commit46-20261022/lean/attempts.json` and the adjacent native receipts.
No new TrustedStd field or other trust item is introduced.

## Stage 2: binary multiproof components

The binary parent group has a finite owned reference, translated through
Charon/Aeneas and checked against native generate/count group logic. The full
sixteen-entry cursor transition also passes: arbitrary strictly increasing
prefix, live cursor and write cursor; exact consumed count, parent, sibling
request and missing-node count; untouched unread suffix after the count-array
write. This is one transition, not a monolithic multiproof gate.

`ProverCommitBinaryGroup46` proves the extracted group equation and symbolic
list-layer/count agreement; its eighteen-level reference emits exactly 32
bytes per counted missing node. `ProverCommitBinaryCursor46` proves the
finite owner reaches the list layer with fuel bounded by input length.
`ProverCommitBinaryInvariant46` proves strict parent order and nonincreasing
occupancy. These results do not yet identify the complete native array/count
loops or their well-formedness guard with that reference.

`ProverCommitTreeSupport46` strengthens the tree interface: every stored
child-map domain, in depth order, is exactly the successive parent image of
the leaf map. `ProverCommitBinarySupport46.stored_requests` proves all
missing siblings requested by any batch subset are covered.
`ProverCommitStoredNode46.constructed_node` derives successful lookup from
that construction; root equality is not substituted for callback coverage.

Two pure D157 fields extend the std boundary in supplemental records in
`ProverCommitStdIndex46`: `TrustedIndex.btree_index` (BTreeMap Index returns
the associated value or panics if absent) and `TrustedSequence.vec_index`
(Vec Index returns the indexed element or panics if out of range). Both are
called at `sim.rs:357`. Consistency witnesses compile. The original shared
TrustedStd24 source/object is untouched. No source callback, interior
mutability, allocation-totality, concurrency or hash law is added.

The callback expression passes Kani under exactly these collection contracts
(1.858 s, 187,088 KiB RSS, zero swap). An initial signature draft fails Rust
compilation. A version expanding the eighteen-element Vec times out at
180 s and is excluded. The replacement uses the per-index std-contract
projection, not an unchanged retry or more RAM. The timeout expired just
before the requested stop reached cargo; kill found no such process. The
time-wrapper RSS for this failed timeout measures its parent only; the
receipt also records aggregate cgroup peak. A live observation saw cargo at
6,377,268 KiB RSS. No successful callback certificate is attributed to it.

The first group harness hit its four-iteration memcmp unwind bound; the
corrected check passes with 36. This is not a Lean resource option or a
proved counterexample. J9645 exposes a backend type mismatch from Rust's
inferred signed shift literal; an explicit `1u32` in the owned reference is
retranslated and passes a new native check. Shipped code is unchanged.
J9646 is a prelaunch dependency refusal with no compilation. Rejected Lean
drafts are retained and never treated as accepted proofs.
