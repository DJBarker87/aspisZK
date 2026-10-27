# Mutable iterator fidelity audit

Work in progress. Headline `AspisR1.RPx_Deployed.deployed`, frozen3 and narrowed D188 retained. No premise removed or changed. Only KSE_ modules and this evidence directory are written.

Stages: (1) generic interval/writeback semantics; (2) kit comparisons and corrected library externals; (3) optimized native differentials and final audit. Budget 80 Lean / 10 Rust / 0 Kani, one admitted capped scope at a time.

The required S2 documents were read at their actual location under `docs/research/100bit-spend-path-20261013/`; the top-level paths in the task are shorthand. KSC2 evidence is absent in this branch. KSA inventory and dependency lists are static dependencies, not runtime reachability evidence.

## Stage 1: generic interval model

`KSE_Interval.lean` models full retained memory and the half-open unconsumed
interval. `selected_bounds`, `trace_bounds`, `no_duplicate_yields` prove bounds
and uniqueness for arbitrary finite mixed schedules. `restoration` and
`restored_slice` identify the final borrowed slice with sequential replacement
of every yielded slot by its final written value; `untouched` proves framing.
Finite schedules include early exit and the completed prefix before a panic.
This is a logical mutable-slot model, not a proof of Rust internals or unwind
Drop behavior. It does not yet associate an existing kit ABI with these slots.

KSE_L001: exit1, ordinary elaboration failure (omega was asked to construct a
conjunction including function equality). KSE_L002 adds explicit constructors:
exit0, wall3.275715159s, peakRSS2647528KiB, swap0; all six roots use only
propext/Quot.sound or no axioms. Exact command/source/dependency/object pins,
revision, limits and full axiom output are in the attempt config and receipt.
Both attempts use the existing unchanged runner and one admitted 6G/8G/Swap0/
Tasks64 scope with -M7000. No timeout or memory kill.
