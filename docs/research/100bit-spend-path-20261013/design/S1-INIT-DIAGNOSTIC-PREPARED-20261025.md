# S1 initialization crash: supported compile-only diagnostic, not run

Status: PREPARED NOT RUN. Native Claims initializedness/allocation/drop/full-loop and whole S1/S6 remain OPEN. No host operation, compiler, solver, backend modification or source/refactor adoption was performed for this diagnostic.

The retained minimal-context uninit-checks attempt fails before SAT at ty_layout.rs:190 without identifying its actual pointee type. Default checks do not cover this, mem-predicates alone bypass initialization checking, and the upstream0.68 primitive-layout branch has no directly observed fix. Do not guess that Never/Infallible/union is the culprit or label these source inspections native proof evidence.

Pinned upstream0.67 code exposes KANI_LOG through EnvFilter::from_env in compiler session setup. UninitPass emits trace!(function=?instance.name(), "transform") before calling UninitInstrumenter::run. The existing --only-codegen option compiles without running verification. These facts support one changed, narrow COMPILER DIAGNOSTIC on the retained failed min-context harness, with no tool binary/backend/native fragment/input-domain change:

- Preserve the exact old command and all its source/feature/stub/uninit/unwinding flags; add --only-codegen.
- Add KANI_LOG=kani_compiler::kani_middle::transform::check_uninit::ptr_uninit=trace to the exact inner environment.
- Retain complete stdout/stderr and source/tool/sysroot/dependency/command/proc/cgroup/status/wall/RSS/peak/swap evidence. The last logged transform function can narrow the crash context; it need not identify the nested offending type and is NOT an initializedness theorem.

The full reviewable argv, basis-receipt hash, expected output, proposed1.5GiB/2GiB/Swap0/Tasks64 controls and prerequisite checks are in evidence/s126-current-caller-20261021/s1-init-diagnostic-20261025/plan.json. The six unmodified upstream source files and exact hashes/URLs/revision are retained. No runtime launcher or admission bypass was added; preparation/check scripts are local and do not contact the host. Metrics/exit status are explicitly null because nothing ran. Source-only audit: `python3 tools/s1-init-diagnostic-20261025/check.py`.

Fresh reviewed allocation/admission, exclusive private source/cache ownership and exact input/tool identity remain required before executing this diagnostic. The current shared policy at lead3b5d6a3dc1 states public API disabled/no general adoption and limits ResourceStableGO to one4GiB rehearsal/tiny marker with no solver/compiler/consumer/native proof. This is not authority to launch the prepared2GiB diagnostic, perturb its observation epoch or use another worker's slot/cache. No host process is started by this packet.

After a genuine diagnostic result, choose ONE smallest changed source isolation based on the observed function/type. Preserve the literal shipped row-write expression, actual private token/error/Box/QM31 carriers and arbitrary complete words; a harness-generation change is legitimate only if its domain/coverage correspondence is established. If the problem is inside the actual shipped allocation/write primitive rather than harness setup, retain it as a tool/source blocker instead of replacing it with a simplified or opaque carrier. Any tool/source candidate requires explicit equivalence/validation/re-pin assessment. No unchanged failed proof or cap rise is justified by this plan.

The new source-selected SDK/caller proofs and their immutable raw data are ready for the lead's coherent original/current kernel/ALL14/event/source/release join. This independent native diagnostic preparation does not assert that join or <=2^-100 per-attempt soundness established. S2 remains transferred and the security target unchanged.
