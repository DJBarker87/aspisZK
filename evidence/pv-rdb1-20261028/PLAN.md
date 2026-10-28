# Deployed native-link repair

Base: 6273e6206164ac60fbc68a49fa888f98b87476f1. Branch codex/pv-rdb1-20261028.
Assigned rows: V164 V170 V178 V181 V182 V183 V184 V186 V187 V195 V198 V219.
Only IDs 54700–54799; audits 54797–54799. Budget 100 Lean, 120 native, zero Kani.
The shared rulings and host-restored flag were read before work. No local Lean.
All builds use one admitted capped scope at a time, 6G/8G/swap0/Tasks64.
No crates/programs changes, no key operations, no push.

Restore only with deployed structural binding, finite native replay and every
needed changed-source law. Retain primitive/world/compiler boundaries explicitly.
First target V186: identical native and reference Vec::new call, followed by
empty-vector observation. Other rows retain unresolved reached edges until resolved.
