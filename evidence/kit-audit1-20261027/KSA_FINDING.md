# Worker-kit audit

Work in progress. No release premise removed. Headline remains
`AspisR1.RPx_Deployed.deployed`; frozen3 and narrowed D188 unchanged.

The definition-by-definition inventory is [KSA_INVENTORY.md](KSA_INVENTORY.md),
with exact hashes, raw-emission comparisons and ambiguity candidates in
[KSA_inventory.json](KSA_inventory.json). Text identity and semantic fidelity
are separate checks. An unproved adapter is UNDETERMINED even if fixtures pass.

Known failures retained: predecessor-indexed `XRn_Join_mpow`,
`XRn_Join_qpow`, and the supplied `aspis_core.field.M31.inv`.
The canonical-input inverse-two disagreement is already proved by
`XSd_InverseCompare.mismatch`; exponent-two collapse by LPo's closed diagnostic.
These concern stand-ins; no shipped Rust or adopted-root defect follows.

Next: focused kernel checks, native frozen differential, theorem-dependency
inventory and import-isolated copies. Budget cap: 60 Lean, 10 Rust, 0 Kani;
one capped host scope at a time. No shipped source change or ELF rebuild.
