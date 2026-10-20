# EbyK push to actual Q.raw coefficient bridge (V17)

This focused Lean target proves that a successful `pushWithDotBackend QRaw` call, together with the canonicality predicate on the value, yields the actual low/high `Q.raw` results used by the EbyK push caller. It pins both calls to `valueLo value` / `valueHi value` and `scalarQ scalar`. Each returned four-word array has the source-shaped `rawC0`–`rawC3` formulas, with every formula input equated to the corresponding low/high value coordinate and scalar coordinate. The eight value-limb bounds are derived from canonicality; successful checked push derives the scalar bound through the existing backend proof.

The target is `EbyKPushActualRawCoefficientBoundsV10`, Lean 4.32.0, standard-only audits, exit 0. Exact source, command, preflight, receipt, GNU time log, admission and reservation evidence are included. Direct source/object pins and the caller snapshot are in `source_import_and_caller_pins.json`. Reused Dot loop/source refinement checker pins are linked to the accepted v2 packet.

This packet does not prove the outer powers-array traversal feeds every generated value to EbyK push. It also does not prove the R22 no-wrap/product-residue guards or the final accumulator update; those remain separate obligations. No production source was changed.
