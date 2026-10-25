# Concrete op5 preflight

Branch codex/cx-op5-concrete-20261025; initial revision
87a79f0184316e40b99d19999669122b63362ae4.
Read the root security/proof discipline, shared/local rules, historical S2
handoff/plan/diagnosis/interface, C3-BIN route-B adoption, Op3I accepted chain,
Op5I accepted batch countermodel, SInt2 coherent-host handoff and Port4B source
and P6 joins. Historical S2 paths resolve under
`docs/research/100bit-spend-path-20261013/`.

Concrete source review: candidate.rs batch_merkle_values calls three trees
in order with shared scratch; batch_tree hashes each opening before immediate
duplicate checking, then checks count/padding/root. Port4B_Install fixes its
children using the documented P6 lowerings. The existing accepted-only theorem
still retains Prepared/model provenance and P6 gates; it does not associate
the arbitrary ChildConeJoin with these effects.

A separate non-vacuity issue needs a focused check: FirstMarks.source is
unconditional over typed op10 returned events, including rejected and even
non-executed events. It requires batch0/query0/save in all those event logs.
The literal shipped tx1 rejects k != SPLIT before any proof, digest or batch
call. A globally faithful source child cannot simultaneously carry those
marks on rejected invocations. This does NOT yet refute success-conditioned
source association only on actual successful accepted occurrences.

Host read-only preflight: approved SInt2 workspace reachable, no populated
build scope besides init.scope. Use unchanged S2W launchers and shared objects;
write only Op5C_ modules/configurations and fresh attempt directories.
Budget 0/80 Lean, 0/40 Kani. No release result: target/exit/time/RSS/swap/axioms
are inapplicable to this inspection. No premises discharged or added.
No shipped files, keys, existing modules or sibling candidates changed;
no ELF trigger, no release replay and no push.
