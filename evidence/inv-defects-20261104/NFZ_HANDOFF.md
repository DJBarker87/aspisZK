# NFZ inventory defect repair

Work in progress. Branch codex/cx-inv-defects-20261104; prefix NFZ_.
Frozen Rust: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.

Scope: independently resolve TX2:046 trait dispatch and TX2:211 callback, scan both cones for related omissions, apply an explicit pinned additive overlay through a prefix-owned inventory producer, and recompute slice membership without promoting any composed status.

Budget: 0 Kani, at most 5 Lean (expected 0), 0 extraction; one admitted capped scratch debug type-check scope. No shipped changes or ELF rebuild. No push.

Authority pending: frozen-source compiler MIR; grep is discovery only. No repair is yet admitted. No security assumption is discharged; D188 trace fidelity remains a trust boundary. Final release target not yet established.
