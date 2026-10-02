# R277 private inverse binding preflight

Read-only inventory of the selected private scalar inverse leaves and candidate existing APIs. This artifact records names, source spans, source hashes, and generated helper availability only. It does not implement a binding or decide that any source/model relationship is established.

The R266 extraction requests `B::neg` and `B::inv` from the frozen `r110_norm.rs`. The decoded source metadata identifies `B::neg` at `12:21–12:61` (`Self::ZERO.sub(self)`) and `B::inv` at `20:4–20:49` (`Self(M31(self.0).inv().0)`). The R230 frozen `r110_norm.rs` SHA-256 equals the source hash recorded by R266. Its neighboring source rows are `B::ZERO` at `7:4–7:28` and `B::sub` at `11:21–11:129`.

The existing R249 adapter declares `B := Std.U32`, `P110`, and `B.sub`; it does not declare `B.ZERO`. The R276 actual translation now contains `B.ZERO`, `B.neg`, and `B.inv` with the source spans above. Its emitted support rows include the source-bound field `P`, `reduce_u64`, `M31.mul`, `square_n` and its loop/body, and the R110 `P110` and `B.sub` rows. The raw R278 adapter under construction is expected to bind the first three private rows to R249/R156 declarations, but this inventory does not inspect or approve that implementation.

R266/R276’s `aspis_core.field.M31.inv` metadata uses name pattern `aspis_core::field::{aspis_core::field::M31}::inv` and span `field.rs:167:4–167:27`. This name and span match the earlier saved R156 generated translation and promoted `AspisR156FullFreeze.FunsCore`. Its visible generated dependency path calls `M31.mul` and `square_n`; the emitted `M31.mul` fallback calls `aspis_core.field.reduce_u64` directly. The actual generated guard uses `massert` and `Std.U32` equality/inequality; no M31 PartialEq helper or `M31.reduce_u64` wrapper appears in this inverse support translation.

`inventory.json` records SHA-256 hashes for the inspected extraction, frozen source, raw R249 adapter, pinned R156 translations, and actual R276 translation. No builds or executions were run for this preflight.
