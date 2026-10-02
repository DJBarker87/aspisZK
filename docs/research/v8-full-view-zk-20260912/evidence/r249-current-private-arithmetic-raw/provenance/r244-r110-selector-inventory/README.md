# R244 R110 selector inventory

Read-only inventory of the frozen R230 private arithmetic leaves in `r110_norm.rs`. No extraction, build, Lean run, test, source edit, or toolchain edit was made. This records mechanical selector evidence only; it makes no semantic or proof claim.

The module path follows the frozen inclusion chain:

`relation_callback::circle_norm` → `circle_norm::joined_inverse` → `joined_inverse::line_norm` → `line_norm::r110_norm`.

The exact include sites are `relation_callback.rs:47`, `circle_norm.rs:6`, `joined_inverse.rs:5`, and `line_norm.rs:85`. The `line_norm` module is cfg-gated under `v8_line_norm` or `test` at the parent include. Accordingly, the candidate plain selectors all use the prefix `crate::circle_norm::joined_inverse::line_norm::r110_norm::` followed by the associated type and method.

The JSON lists all 17 requested selectors and the direct dependencies visible in each method. The selected method set includes `B::{input,add,sub,half,mul}`, `C::{input,output,add,sub,half,mul_m,mul,square,times_r,norm}`, and `Coeff110::{new,four}`. Their important closure points are `B::reduce` (reached by C multiplication/square/norm), `C::double` (called by the local `polar` closure in `Coeff110::new`), and the file constant `P110`. The requested list does not include those extra method roots. `B::neg`, `B::inv`, and the `batch`/`try_norm` path sit outside these method bodies and may matter only for a broader extraction.

These are plain `Type::method` paths. The pinned Charon Rust resolver traverses later path components through `nameable_children`; its `full_def.rs` documents inherent items among type children. Inherent impl brace patterns are unsupported as `--start-from` roots, so no brace syntax is proposed. This supports the candidate syntax by source inspection; it does not prove that private nested names resolve in an extraction.

There is a separate order risk after path resolution: Charon's reorder pass seeds declaration ordering by matching the textual `start_from` pattern against emitted names. Previous R231 inspection found that inherent-method emitted names contain an impl path element while the matcher returns false for inherent impl elements. Thus a resolved plain selector is not evidence of nonempty `ordered_decls`; ordering metadata must be audited separately.

`Coeff110::new` uses two immediate local closures (`norm` and `polar`), `Option` and `?`, destructures a `[K; 3]`, and builds `[C; 5]`. `Coeff110::four` indexes `[C; 5]` and returns `[C; 4]`. Those closure, Option/try, and fixed-array translation boundaries could add dependencies. The direct arithmetic globals and field calls are enumerated in `inventory.json`; no field meaning or theorem premise is selected here.

Pinned Charon revision and source hashes, the frozen source/provenance hashes, exact line references, and the full dependency inventory are in `inventory.json`. Frozen source root has no Git metadata; the launch campaign revision recorded by R230 provenance is `07977092976005ff691cf381d3e539d3ac06b595`.
