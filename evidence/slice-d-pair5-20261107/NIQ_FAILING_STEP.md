# NIQ failures and replacements

L001 diagnostic inspection: exit1, unknown unqualified FIn_Primitives.field name. Imported functions resolve; the qualified owner is AspisR1.FIn_Primitives.field. No theorem or proof credit; diagnostic source excluded from imports.

K001: compile rejection before proof, allocator_api feature missing for exact KMX_stubs.rs inclusion. Own scratch preparation now adds the same cfg(kani)-only allocator_api feature attribute as NIG. K002 uses unchanged property/name with corrected own preparation. No timeout/memory retry or shipped mutation.

NIG L079 allocation model draft repaired in NIQ_AllocationError: expose local alpha abbreviation to rewrite at each bind explicitly, rather than broad simp failing to match local let. L003 exit0 and standard axioms; no predecessor edit.

K004 allocation_owner: default builtin memcmp loop unwinding failure from fixed-array equality, not a semantic counterexample or timeout. K005 replaces array equality with an arbitrary selected limb observation (extensional assembly), avoiding memcmp without changing caps or solver timeout. Native prefix remains64, not a short-vector restriction.

L014: raw ax2 all22 roots standard; scanner exit1 solely because own seven new import baselines omitted implicit Init. Zero dangling/duplicate owners. Own source-derived catalog repaired to include implicit Init, preserving order/dedup and exact equality predicate. L015 replays ONLY scanner with the changed catalog; raw proof walk is not rerun. Original scan retained as NIQ_L014_LOADED_scan.jsonl.xz/.sha256.

Scope hygiene: invoking the inherited NIG validator unchanged regenerated its two existing validator-output JSON files in the same worktree. Their bytes match committed files (no git diff); no sibling/live worktree was touched. This exceeded the intended read-only evidence discipline. Subsequent predecessor checks use only the unchanged pure gate via AST with outputs under NIQ.

Packaging: cfg(kani) allocator_api attribute moved from the preparation script into NIQ_gap_cuts.patch. NIQ_PATCH_EQUIVALENCE.json checks every generated input byte against successful K007 source snapshots; no proof-body/configuration change or rerun. The failed inspection file is retained as .diagnostic.lean.txt, outside the import closure.
