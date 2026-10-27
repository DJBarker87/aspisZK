# Import measurements and module-system obstruction

All six single/pair probes were checked sequentially with -M7000 and the
required 6G/8G/Swap0/64 scope. Sources/commands/revisions/object hashes and
measurements are in per-attempt receipts. No failed source was rerun.

Tree0/1/2: 6926116/6889556/7008340 KiB. Pair01:7065480 KiB PASS;
pair02:7171056 KiB exit134 internal Lean memory failure;
pair12:7146640 KiB PASS. All swaps0. Prior JGw011 three-tree failure reused.
Every module in the three trees' source closures is inventoried in
JGy_TREE_CLOSURES/SOURCE_CLOSURES/OBJECT_SIZES.json. Certificate objects total
589069952/487228976/419237880 bytes respectively; the source closures also
contain large older JFm/JGa certificate families. Sizes are selected .olean
sizes, not a claim that every byte is resident.

Attempt007: pinned Lean4.32 rejects the requested module experiment immediately:
`cannot import non-`module` JFp_SHABlocks from `module``.
Lean Environment.lean2057-2066 explicitly forbids a module root from importing
legacy modules. Merely adding public import cannot hide these legacy closures.
No toolchain change or existing-module edit is authorized. The failed source
is retained in007/sources and JGy_MODULE_UNAVAILABLE.lean.txt; it is not shipped
as a valid module. No importer RSS improvement is claimed for this route.

Fallback: inspect existing per-round proofs (008), then replace expanded
rewriting chains with named generic fold applications in NEW JGy modules.
No top premise removed: FJv83T/3P/13G unchanged; no accepted-pair non-vacuity.
Latest ledger separately books historical L187, so its current deployment
baseline is89T/18P/13G, not the previous handoff's89T/19P/13G.
No shipped files changed; inherited ELF pins only. No Kani/Rust/ELF run.
