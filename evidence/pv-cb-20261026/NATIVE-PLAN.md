# Native source correspondence work

The first checked equations are value interpretations, not native refinement.
P6 must connect unchanged shipped calls to an owned safe reference and extract
that reference before any full row removal. Native ABI/world/compiler transport
and the endpoint root remain separate. No success is inferred from matching
names, installation equations, or shared object availability.

The standalone proof crate is cfg(kani)-only. First gates: mem::take (arbitrary
u64 and nonzero custom Default), PathBuf deref/AsRef (arbitrary Unix bytes,
length0..16), String AsRef (all valid UTF-8 among byte vectors length0..16),
Path::join (arbitrary Unix byte prefixes/suffixes of lengths0..8). No stubs.
These bounds must remain explicit; no bounded gate is a universal native proof.
Expected time: Kani compilation/model checking, not dense arithmetic. Charon
reference extraction is a separate capped optimized build.

A pre-admission scan at2026-10-26T13:15:33 refused:60532195328 reserved bytes;
8589934592 requested;69122129920 projected;59055800320 safe limit. No Kani
attempt charged. Three-minute retry required. Full host receipt retained under
codex-pv-cb-20261026/kani-take-001; stdout redirected before source transfer.

Review of initial op26 deferral: allocator behavior is real native state, but a
safe reference can preserve the same allocation route for a bounded value gate.
Therefore allocator dependence alone is not a reason to abandon the independent
value law. The checkpoint's deferral is provisional and P6 work continues.
