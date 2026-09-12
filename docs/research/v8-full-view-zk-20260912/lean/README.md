# Lean generic privacy foundations

The supplied first attempts were repaired for the repository's pinned Lean
4.32.0/Mathlib API without weakening theorem statements. All thirteen generic
modules, the aggregate, the exact pinned `FSOracleExecution` source and the FS
integration draft compile. See `../evidence/VALIDATION.md` for the commands,
resource envelope and axiom summary. This remains leaf-level evidence, not a
source-instantiated privacy theorem or independent kernel replay.

## Module map

| Module | Attempted result | Boundary |
|---|---|---|
| `FiniteGames` | Finite uniform law transport by a concrete coin bijection | No actual seed/oracle distribution |
| `AffineMask` | Fixed affine mask translations and dual separation | Pairwise WI, not public-input ZK |
| `BalancedMasks` | Explicit bijection onto one zero-sum hyperplane | Source row adapter absent |
| `ConditionalMask` | Joint corrections and kernel-to-fiber parametrization | Source maps and conditional uniformity must be constructed |
| `PositiveOverwrite` | Active-coordinate overwrite leaves an inactive sum unchanged | No hiding theorem |
| `DCompensation` | Fixed nonzero-gamma algebraic compensation and sum preservation | D's own disclosures and commitment chronology are not fixed |
| `RetrySymmetry` | Finite first-hit controller, renaming and stopping count | No hash-tape law |
| `Visibility` | Public-event projection and exclusion of direct private events | No assertion that later public values reveal nothing |
| `AdaptiveComposition` | Equality of genuine conditional kernels composes | Actual source kernels/equalities not supplied |
| `GatedRelease` | Gate-preserving transport including explicit abort | Actual rank-gate caller and coin transport unproved |
| `PrivacyGames` | Statistical/ computational targets and simulator cost target | Definitions only; no simulator or advantage theorem |
| `HybridBudget` | Event-distance triangle and exact same-game hop | No numerical V8 privacy bound |
| `SeparatorObstruction` | A same-public efficient separator larger than `2ε` rules out any one statement-only `ε`-simulator | No V8 same-public witness pair or source event instance is asserted |
| `V8Profile` | Literal inventory/wire arithmetic | Numeric identities, not source authentication |
| `AspisV8Privacy.lean` | Aggregate imports | Not a capstone security theorem |
| `integration-drafts/FSProgrammingDraft` | Conflict-detecting chosen requests using the **actual existing FS types** | No programmed-oracle law or prover refinement |

The finite-distribution layer intentionally uses nonempty finite coin spaces. Computationally bounded tests and simulator efficiency are distinct targets. Do not use an unrestricted statistical target for a fixed short-seed PRG without an appropriate theorem.

## Compiling safely

Use the repository's existing Lean 4.32.0/Mathlib environment. Compilation was
serial with `-j1 -M1800`, into a temporary output directory. No dependency was
downloaded and no package-wide build was run.

Some imports/tactic names or elaboration details may need adjustment for the repository's pinned Mathlib version. Repair them without changing theorem statements or hiding necessary hypotheses. The mathematical claims should be reviewed independently of whether Lean accepts the script.

A successful leaf compilation using imported `.olean` files is **not** a fresh rebuild/replay of those dependencies. The runner reports this explicitly. It does not certify an historical/patched Lean binary or execute an independent kernel checker.

## Existing FS integration

`FSProgrammingDraft.lean` imports `FSOracleExecution` from completion commit `ab4f61feaca096ae3dae66e39d29f6e36bdca0ec` at:

`docs/research/v8-completion-fs-extraction-20260911/lean/FSOracleExecution.lean`.

Build that exact source/dependency closure in an isolated compatible overlay and retain its pin. Do not satisfy the import with another module of the same name or new shadow types. The generic leaf runner deliberately does not build this integration draft.

The helper forbids overwriting incompatible existing answers. It does not prove that selecting a fresh answer preserves any random-oracle law. That remains a genuine cryptographic proof obligation.

## Do not promote target definitions

`FullViewSimulationGoal`, `ComputationalFullViewSimulationGoal`, `SimulatorCostGoal`, `SeedExpansionHybridGoal` and `SourceExecutionAgreementGoal` state what a future construction must establish. They are not evidence that the construction exists. Do not satisfy them with a premise that already assumes the desired result or by defining the “real source” to equal the model.
