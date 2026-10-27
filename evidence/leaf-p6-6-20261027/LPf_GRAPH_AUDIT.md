# Frozen graph audit

Before each Kani invocation: offline locked cargo metadata; every resolved package
and edge checked against the frozen Cargo.lock; lock hash checked before/after.
Additionally the normalized full 441-package resolved graph (all edges, independent
of scratch absolute path) is equal to the retained frozen LPe_G001 graph.
LPf_frozen_graph.json records that exact graph. G004–G012 were checked retrospectively
while K012 was running; all match. The graph equality is now a mandatory prelaunch
gate too. The lock contains444 entries, of which441 are resolved by the frozen
metadata configuration; no441=444 claim is made.
