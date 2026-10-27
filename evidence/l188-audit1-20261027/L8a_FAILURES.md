# Retained diagnostic failures

L8a_003 (first Lean compile): query used `env.checked.get.toList`; Kernel.Environment has no toList projection. No inventory executes; the two preceding #print axioms results are retained. Corrected source enumerates `env.toKernelEnv.constants.toList`, the existing RPz8 audit API. No timeout or memory failure. The changed query is a new attempt, not an unchanged retry.

L8a_004: ExternAttrData has no Repr instance. Changed query records presence of the extern attribute (the requested declaration inventory), without fabricating an attribute value. No inventory executes before this elaboration error.

L8a_005 exits 0 and emits a complete inventory, but `Name.getString!` panics on numeric final name components. The inventory is diagnostic, not a clean gate pass. Replaced partial last-component inspection with total pattern matching in the new L8a_SurfaceInventory module. Also the copied job receipt adapter's optional query-object view install failed after receipt collection because this job has no overlay directory; no shared view changed. Query-only objects have no downstream consumer, so removed that optional publish step from the job adapter rather than creating another overlay. Existing S2W launchers, monitors and reservation tools are unchanged.
