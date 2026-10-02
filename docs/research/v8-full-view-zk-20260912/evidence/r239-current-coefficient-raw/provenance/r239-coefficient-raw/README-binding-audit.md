# R239 raw coefficient binding audit (mechanical)

Read-only comparison only; no Lean/build/test or source/toolchain edits were performed. This is declaration-text evidence, not a source-semantics or theorem-premise conclusion.

## Result and stop condition

All seven R239 leaf definitions match their R238 generated leaf blocks after whitespace normalization, with exactly the two explicit M31.half literal API adaptations listed below. The two coefficient aliases and the M31/CM31/QM31 layouts match the pinned R156 generated declarations after whitespace normalization.

Direct project-qualified function calls in the seven raw leaf bodies are `CM31.add`, `CM31.sub`, `M31.mul`, `circle_norm.norm`, and `circle_norm.polar`. R238 `CM31.add` and `CM31.sub` blocks match R156; R238 `norm` and `polar` blocks match the pinned R221 raw adapter. **The comparison found one unexpected difference and stops here:** the R238 generated `M31.mul` block differs from pinned R156 `FunsCore.lean` at its shift-count literal:

- R238 generated: `Std.U64.wrapping_shr x 31#i32`
- pinned R156: `Std.U64.wrapping_shr x 31#u32`

This is outside the two authorized M31.half adaptations. No attempt was made to normalize or justify it. The R239 raw adapter imports/opens R156 and R221, not R238 Funs; therefore its direct unqualified `M31.mul` name resolves via the pinned R156 import. The mismatch still blocks the requested full generated-to-pinned binding audit until the lead decides how to handle the R238 discrepancy. No recursive audit beyond the existing R221/R156 bridge evidence was undertaken after finding it.

## Exact half adaptations

`build_raw.py` adapts only these two literals in `aspis_core.field.M31.half`, once each:

- source generated expression `Std.U32.wrapping_shr self 1#i32` → raw adapter `Std.U32.wrapping_shr self 1#u32`; corresponding statement is `count_one : (1#i32 : I32).bv.toNat = (1#u32 : U32).val`.
- source generated expression `Std.U32.wrapping_shl i1 30#i32` → raw adapter `Std.U32.wrapping_shl i1 30#u32`; corresponding statement is `count_thirty : (30#i32 : I32).bv.toNat = (30#u32 : U32).val`.

The R239 `M31.half` body is text-identical to the R238 body after applying those exact replacements. Its indirect field use is `CM31.half`, whose body matches R156 and calls `M31.half` on `self.a` and `self.b`.

## Existing boundary evidence

R239's `circle_norm.norm` and `circle_norm.polar` references compare exactly to the pinned R221 raw definitions. The existing `.r21-scratch/r221-norm-leaf-translation/shared-operation-binding-audit.json` records normalized equality for its eight shared R156 field operations: M31.double/sub/add and CM31.new/square/sub/mul/double. This is the boundary cited here; the audit does not make a new transitive semantic claim.

Full per-declaration normalized hashes, direct-call inventory, layout comparisons, source-file checksums, and the exact M31.mul token difference are in `binding-audit.json`. Raw source excerpts for the adapter instructions, all seven leaves, layouts, and mismatch are in `binding-audit-excerpts.txt`.
