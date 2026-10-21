# S10 pass 2

Frozen inputs and first-pass evidence remain read-only under
`../s10-inventory-20261021/`. New scripts are in
`tools/s10-inventory2-20261021/`. No shipped source changes are planned.

The rustc probe visits one selected Pool module per invocation, after type
analysis, and records optimized MIR calls with source spans, generic arguments,
indirect calls and drop types. The verifier may use a whole-crate probe.
This uses the pinned Charon nightly (1.98.0-nightly, 14210df0e), independently
of Charon lowering. It is diagnostic native/forced-cfg evidence, not SBF
source equivalence. Only corroborated edges or ELF-confirmed edges qualify.

Each host probe must use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64, a reservation preflight, and a timed receipt. Derived JSON over
5 MB is represented by SHA-256, size and generator, never committed.

The completeness gate must retain unresolved semantic frontiers. Ownership
assignment and source completeness are separate checks; neither discharges
AcceptedRunJoin or the security target.
