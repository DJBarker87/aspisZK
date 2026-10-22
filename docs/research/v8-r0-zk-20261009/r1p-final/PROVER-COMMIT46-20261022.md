# Prover commitment continuation 46

Target not yet established. Base 4a7c0512e (LOG D158), branch
`codex/cx-prover-commit46-20261022`. Work proceeds under D158's explicit
state-passing interpretation of ProgramOne; no interior-mutability trust law
is authorized or introduced. D143 observables, the D146 statement domain,
and adversarial environment/public nonce remain the intended contract.

## Stage 1: ProgramOne state transition (in progress)

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
