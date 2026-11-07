# LIBB TX2 library handoff

Target not yet established. Branch codex/cx-libb-20261107, base 198f29a487ce5a72061c3ff09063c8cf176e7f11.

Scope: LIB0 modules 6–13, in order. Budget 300 serial Lean/link/audit scopes, 0 Kani, 0 extraction. First expected cost is import elaboration and private cache validation, not arithmetic normalization. RSL revision 3 is the target; F1 reads Env.reservation. Frozen sources and trust rows remain unchanged. No row is credited here; ledger gate decides.

Reuse: merged LIB modules 0–5 and 6 are imported, never re-proved. Partial registry/account support is inspected before adoption. All new sources use LIBB_. Seed ledger25 retained export and coherent paths into a private retained cache; record copied object hashes and selected Aeneas objects. One scope at a time, 6G/8G/swap0/tasks64, Lean -M7000, fresh share/disk/admission checks.

Validation pending. No new hypotheses discharged or added. Next deliverable: module 6 import and carrier interface, then registry module.

Module 6 imported unchanged via LIBB_PoolCarriers; L001 exit0, 19.528s, peak6460896KiB, swap0; standard axioms only. Carrier choices DONE, no new source equivalence or principal credit.
