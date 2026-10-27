# Library row table

Candidate source callback laws supplied: **0 → 4** (V177/V180/V185/V186), through `PV_CBL_CallbackBundle`. Native P6 bounds and the distinct extraction/Kani toolchains remain explicit. The canonical recount and endpoint are not edited here; RunJoin/deployment integration remains open. Target not yet established.

| op | row | status | theorem | crate/version; source hash | receipt |
|---|---|---|---|---|---|
| 205 | V231 | OPEN; queued | — | `sha2-0.10.9/src/core_api.rs` sha256 `73b160d98bfa6737688875ad73da5e3c2c93582604dc313d208200e12fdab676` | — |
| 208 | V232 | OPEN; exact body decomposed, compress256 binding retained | PV_CBL_Op208Shape.extracted_shape (not source closure) | `sha2-0.10.9/src/core_api.rs` sha256 `73b160d98bfa6737688875ad73da5e3c2c93582604dc313d208200e12fdab676` | — |
| 209 | V233 | OPEN; pure split specification prepared; extracted bridge pending | — | `block-buffer-0.10.4/src/sealed.rs` sha256 `9327ee3e567ae779b83c2b7f4f3ff56fcb2117163e023e7b0e37759e7e8d1f5c` | — |
| 212 | V234 | OPEN; extraction frontier retained | — | `digest-0.10.7/src/digest.rs` sha256 `8beab74640774c9f6811daa6dac9b5a8867f5beeb0b552a9b5ddbc5cfc196ed0` | charon/aeneas-source-op212-* (no law) |
| 215 | V235 | OPEN; mono extraction missing callee (wrapper.rs:173) | — | `digest-0.10.7/src/core_api/wrapper.rs` sha256 `033777bed7d140b158e15d50fda8a6e06557ce89bd0738fcca692be2c39e8b8a` | — |
| 216 | V236 | OPEN; queued | — | `digest-0.10.7/src/core_api/wrapper.rs` sha256 `033777bed7d140b158e15d50fda8a6e06557ce89bd0738fcca692be2c39e8b8a` | — |
| 217 | V237 | OPEN; queued | — | `digest-0.10.7/src/core_api/wrapper.rs` sha256 `033777bed7d140b158e15d50fda8a6e06557ce89bd0738fcca692be2c39e8b8a` | — |
| 219 | V238 | OPEN; queued | — | `digest-0.10.7/src/core_api/ct_variable.rs` sha256 `703bd62fb693a437e319d1192988bd674f9127a6b76f73b4c58c71afc79bc013` | — |
| 25 | V177 | SOURCE LAW SUPPLIED; P6 bounded native check | R1Z.PV_CBL_CallbackBundle.op25_source | `std/src/path.rs` sha256 `14fd41348e74555af61dacf60bd78edc9cd2ea534abdad3266854a9a0b696886` | 39647/39648/39650; kani-pathbuf-borrows-r01 |
| 26 | V178 | OPEN; queued | — | `std/src/path.rs` sha256 `14fd41348e74555af61dacf60bd78edc9cd2ea534abdad3266854a9a0b696886` | — |
| 28 | V179 | OPEN; queued | — | `std/src/path.rs` sha256 `14fd41348e74555af61dacf60bd78edc9cd2ea534abdad3266854a9a0b696886` | — |
| 29 | V180 | SOURCE LAW SUPPLIED; P6 bounded native check | R1Z.PV_CBL_CallbackBundle.op29_source | `std/src/path.rs` sha256 `14fd41348e74555af61dacf60bd78edc9cd2ea534abdad3266854a9a0b696886` | 39647/39648/39650; kani-pathbuf-borrows-r01 |
| 30 | V181 | OPEN; queued | — | `alloc/src/string.rs` sha256 `d320cfe75e8962583e54f4094648a7d981684749f9eb65f46cceaedb1de8916d` | — |
| 31 | V182 | OPEN; queued | — | `alloc/src/string.rs` sha256 `d320cfe75e8962583e54f4094648a7d981684749f9eb65f46cceaedb1de8916d` | — |
| 32 | V183 | DEFER(pv-runjoin): recoverable native allocation effects | NATIVE-EFFECTS.md | `alloc/src/vec/mod.rs` sha256 `a9cfdfc0aeb91ccbe2e382784df6c6b4533dd07c7ed979f782069f784996729f` | — |
| 33 | V184 | OPEN; queued | — | `alloc/src/vec/mod.rs` sha256 `a9cfdfc0aeb91ccbe2e382784df6c6b4533dd07c7ed979f782069f784996729f` | — |
| 34 | V185 | SOURCE LAW SUPPLIED; P6 bounded native check | R1Z.PV_CBL_CallbackBundle.op34_source | `alloc/src/vec/mod.rs` sha256 `a9cfdfc0aeb91ccbe2e382784df6c6b4533dd07c7ed979f782069f784996729f` | 39604–39610; bundle 39622; kani-op34-exact-006 |
| 35 | V186 | SOURCE LAW SUPPLIED; native default check | R1Z.PV_CBL_CallbackBundle.op35_source | `alloc/src/vec/mod.rs` sha256 `a9cfdfc0aeb91ccbe2e382784df6c6b4533dd07c7ed979f782069f784996729f` | 39611/39614/39622; kani-op35-exact-002 |
| 36 | V187 | OPEN; generic copy extracted, complete wrapper rejected; ARRAY-FRONTIER.md | — | `alloc/src/vec/mod.rs` sha256 `a9cfdfc0aeb91ccbe2e382784df6c6b4533dd07c7ed979f782069f784996729f` | — |

Std/alloc source corpus: rustc **1.98.0-nightly (14210df0e, 2026-05-31)**, toolchain nightly-2026-06-01. Kani gates use their separately pinned rustc **1.93.0-nightly (53732d5e0)**; no deployed std/ELF association is inferred. Cargo library rows use the versions in the file column. Full source SHA-256 values above are retained.
