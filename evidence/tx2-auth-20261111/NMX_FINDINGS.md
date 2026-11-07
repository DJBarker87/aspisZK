# NMX findings and boundaries

No row credit. Target not established.

* NMX-F1: The reused NMS233 interface is an interface draft, not a native allocation bridge. Its stopped clauses require the VALUE trace `NLM_Auth233.G` to stop at the same place. That trace has no separate final `Box::new(live_snapshot)` operation; fresh E002 also erases that allocation. The full source program therefore keeps an explicit `snapshot` command, admitting a stopped prefix there. The nominal SourceModel is explicitly only the normal allocation value path. A canonical std/allocator interpretation and an exact stopped-prefix refinement must be installed before claiming equivalence to the published interface. This is an inspection obligation, not an exhibited reachable frozen counterexample or a new trust request. Under(bl)(3), no post-abort heap/cleanup is required.
* NMX-F2: NMM snapshot248cb653b077 has no217/234 RowSpec/root. Its support statements are not candidate packets and cannot be cited as one. New NMX_FullChildren statements keep FULL boxed217 results, malformed extents, all234 arguments, full external frame/effects and stops. They are intermediate packet schemas; generic handler/ClosedPackets premises are forbidden in a row root.
* NMX-F3: The parametric full-source program and fold must be connected to actual E002 control/value and canonical child owners. Fresh-emitted value equality alone, nominal Box labels alone or ClosedPackets as a hypothesis cannot close233. Every unapplied native owner/domain is listed in REMAINING.

No(bc)-flagged owned exit exists, so no Kani run is authorized/needed for this row. No field products, copy-dependent native pass, function pointer, writable static, shipped edit or trust-row edit was attempted.
