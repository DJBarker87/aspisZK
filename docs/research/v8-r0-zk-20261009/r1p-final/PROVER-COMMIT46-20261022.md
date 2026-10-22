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
