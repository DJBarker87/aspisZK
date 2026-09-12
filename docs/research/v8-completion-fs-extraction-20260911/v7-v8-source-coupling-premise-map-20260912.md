# V7 to V8 source-coupling premise map

The inspected V7 leaves do not yet instantiate the V8 whole-script alignment
for an actual adaptive source/adversary run.

| V7 theorem | What it produces | V8 relevance | Missing premise/interface |
|---|---|---|---|
| `run_machine_with_uniform_tape_preserves_fresh_exposure_bound` | `WithinFreshAnswerTape` for `runMachine (controllerFromFreshAnswerTape ...)` from an arbitrary initial state | Supplies fresh-count/tape bounds | Requires an already supplied finite tape controller; does not construct the deployed/adversarial source tape |
| `run_machine_with_uniform_tape_preserves_fresh_history_contents` | Exact `FreshHistoryMatchesTape` consumed prefix | Supplies the V8 content field | Same ideal-controller premise; no arbitrary adaptive-source law or prehistory |
| `projected_machine_prefix_steps_le_fuel` | V7 projected-prefix step bound | Resource/fuel input only | `ProjectedMachinePrefixReturned` and `controllerFromProjectedFreshAnswers` are V7 stage objects, not the current `Script`/`FSOracleExecution` state |
| `returned_concrete_restoration_client_has_exact_state_map` | `ActualRestorationStateMapInvariant` over a returned restoration trace | Tracks V7 scheduler/restoration state | Requires root closed/Q16/K13/challenge invariants, concrete restoration client, and V7 `UnifiedExposureRecord`; no `projectOracleState` or current byte-log equality |
| `completed_full_run_has_exact_operational_resource_certificate` | Exact V7 completed-root factorization | Gives query/fuel/resource caps | Requires `ExactFixedCleanCompletedRootPackage` and fixed compiler projection; caps do not imply fresh-only table provenance |
| `exact_fixed_legal_subset_operational_input` | Fixed clean event implies proof-relevant V7 operational input | Event-side reduction only | Requires fixed Tag-73 ROM/configuration, transition-room, driver coverage, reserves, and cutoff; not generic over V8 scripts |

The V8 adapter already proves the deterministic endpoint once the following
facts are available for a V7 state: history-total coherence, no programmed
entries, fresh-count/content/tape bounds, and compatibility with a Nat-indexed
tape. For the ideal `runMachineFromUniformFreshTape` from `emptyOracle`, those
facts are now constructed internally. For an actual source/adversary run, the
first missing producer is a theorem that exposes its ordered fresh-answer
history and table provenance as a finite `FreshAnswerTape` controller (or an
equivalent coupling relation), while preserving cached answers and aborts.

None of the four inspected fixed V7 modules supplies that producer. Their
objects are either resource certificates, fixed Tag-73 completed packages, or
restoration-state maps with V7-specific transcript/Q16 invariants. Adding a
generic wrapper would therefore hide the genuine adversary/distribution
premise rather than close the source-coupling gate.
