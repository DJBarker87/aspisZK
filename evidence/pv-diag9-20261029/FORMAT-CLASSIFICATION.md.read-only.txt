# D414(e): op227 formatting / D159 observer classification

Status: source/LLBC and deployed-configuration LLVM inspection, with exhaustive
immutable-table guards. No honest-run formatting finding identified in this
cone. This does not close D348 or the complete D159 observer obligation.

The listed Write vtable methods are **unreachable from op227**, rather than
inherently panic-only functions. The formatting-related runtime calls which
remain in the inspected op227 cone are panic-only. Compiler glue remains at
D381/D386; nothing is added to T.

## Exact LLBC origin and callers

`format227-llbc-resume7.json.xz` retains the three inventories and exact call
nodes, spans, argument strings, generic formatting bodies and vtable global.
In compstdcone the corresponding IDs are209,212–215; partsstdcone208,211–214;
stdcone203,206–209. Their Rust origin is the blanket implementation
`impl<W: Write + ?Sized> Write for &mut W` in core/src/fmt/mod.rs, extractor
lines246–257. These are compiler-generated thunks/initializers, not separately
written Rust methods.

|Declaration|Exact immediate LLBC relation|Branch reachable from op227|
|---|---|---|
|`core::fmt::{vtable}`|global43 initializer calls function209; global43 is referenced by function194 `core::fmt::Write::write_fmt::spec_write_fmt`, in the `else` of `args.as_statically_known_str()` (the `fmt::write(self,args)` conversion to a dyn Write)|No call path from op227 to194; the table is included as a trait/body dependency|
|`core::fmt::{vtable_drop_shim}`|function209 installs function212 in its drop slot|No runtime op227 caller|
|`core::fmt::write_str::{vtable_method}`|209 installs213;213 calls206, the blanket `write_str`, which forwards to `(**self).write_str(s)`|No runtime op227 caller|
|`core::fmt::write_char::{vtable_method}`|209 installs214;214 calls207, the blanket `write_char`, which forwards to `(**self).write_char(c)`|No runtime op227 caller|
|`core::fmt::write_fmt::{vtable_method}`|209 installs215;215 calls208, the blanket `write_fmt`, which forwards to `(**self).write_fmt(args)`|No runtime op227 caller|

The application-side LLBC formatting-argument constructions have exact callers:
`reference_copy_terminal::link_weight`, default arm of `weight_kind` outside
0–4, constructs the fixed "generated Pool V1 pair-forest Copy weight" panic;
`reference_copy_terminal::selector_mask_sum_16`, default arm outside
1749/2048/2049/4097/6144/6145/26214, constructs the fixed "outside frozen active
mask set" panic. The latter is an owned-reference transformation, not a shipped
success-path print. All64 frozen masks lie in those seven cases. Generic
`Write::write_char` reaches `char::encode_utf8_raw`; its insufficient-buffer
panic and the formatting/raw-slice precondition abort functions are in the
formatting implementation dependency closure, with no op227 runtime call path.

## Native LLVM caller/branch evidence

The three capped optimized native compilations use rustc1.94.1, the deployed
resolved features/versions and release overflow/debug settings. They emit the
unchanged shipped cost-probe, statement and core crates. This is freshly emitted
**deployed-configuration library LLVM**, not a claim to have recovered IR from,
or re-pinned, the deployed executable. Exact source/configuration hashes,
commands, resource receipts and artifact hashes accompany this document.

`llvm227-trace-resume7.json` and `llvm227-op227-resume7.ll.xz` retain the
reachable definitions, direct edges, panic blocks and predecessor branches.
The root is `aspis_r1_cost_probe::host_public::terminal_qm31`; its inlined
`host_terminal::r0::Public::terminal_qm31` calls `host_terminal::composition_parts`.
There is no indirect call or reachable formatting vtable. The only external
non-intrinsic leaves are bcmp and the named panic routines.

|Rust caller and branch|LLVM evidence / why unavailable on an honest run|
|---|---|
|`host_copy_terminal::pattern_values`, `openings[usize::from(pattern.columns[limb])]` bounds failure, inlined into `host_terminal::composition_parts`|`panic9.i.i.i`; predecessor `bb12.i.i.i` tests column `<16`; all14x16 column fields are in0–15|
|`host_copy_terminal::link_weight`, default `weight_kind` arm, inlined into composition_parts|`bb1.i.i`; predecessor `bb4.i542` switches on immutable weight tag with cases0–4; all136 tags satisfy it; panic text is fixed, with no witness values|
|`host_copy_terminal::accumulate_endpoint` → `Selectors::row`, high selector bounds failure|`panic.i`; predecessor `start` tests immutable endpoint row `<1024`; all272 endpoint rows satisfy it|
|`host_copy_terminal::accumulate_endpoint`, weight/value slot bounds failure|`panic`; row-success predecessor tests immutable slot `<2`; all272 slots satisfy it|
|`host_copy_terminal::accumulate_endpoint`, pattern index bounds failure|`panic2`; predecessor `bb2` tests the packed pattern index against14; all272 pattern fields are in0–13|
|`aspis_core::field::qm31_m31_dot`, `assert_eq!(weights.len(),values.len())` failure|`bb2`; predecessor compares lengths. Both actual calls from `state_only_poseidon::interpolated_internal_pair` pass literal LLVM lengths7/7. Rust uses the same fixed seven-element ROWS array for all three map results|

`format227-constant-guards.json` records every table field and equality of the
owned and shipped constants. The guards depend on these immutable fields or
fixed lengths, not on witness words, claims, point, challenges, append index or
variant. Arithmetic branches inside the blocks are not formatting branches.
Each panic block is noreturn/unreachable after its panic call. No successful
op227 result returns a string or emits stderr/log output in this inspected cone.
A panic runtime can print on a panic: it is **not** assumed silent.

## Credit and remaining boundary

This is a checked source/LLVM classification, not formal termination of the full
reference, a complete shipped-to-owned binding, or closure of all pre-inline std
semantics. It does not discharge runjoin's op227 hypothesis. Semantic uses of
Charon/Aeneas are **reclassification within existing tool trust**. The wider
log/error observer gap D348 remains open; no simulator or observer is weakened.
