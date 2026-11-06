# Findings and input repairs

NJS_K001: pre-proof compile failure (missing frozen cfg(kani) tools/r1-builder-reference/tree.rs). Added the existing NJE frozen supplement with independent SHA256 and Git-blob validation to the OWN gate; no shared script changed. NJS_K002 is the repaired input attempt. No solver timeout/memory kill or verdict was renamed.

NJS_E001: one extraction completed (exit0); all twelve candidate targets have emitted definitions. The two aspis_core start-from entries did not make dependency definitions transparent: private_leaf is an external signature; parent is absent. This is an extraction coverage limitation, not emitted-body closure. Do not spend a second extraction; inspect retained canonical NDH emissions before using either leaf.

L002 found missing section-variable arguments in nested emitted calls and two I32 shift literals where the pinned library expects U32; L003 confirms only the two literal annotation repairs remained. NJS_parameterize.py now threads parameter closure syntactically and changes exactly two 8#i32 annotations to8#u32. Raw output is unchanged; L004 compiles the result. L005 only failed on an exploratory #print of nonexistent UScalar.eq, removed for L007. No failed module is credited.

NJS_L017 first preparation stopped before compiler submission: direct import NDI_BatchWord.olean absent in resolved paths. The exploratory KeyWord module did not require this import, so it was removed; the same unused attempt ID is launched only after this input fix. The original admission is kept as NJS_L017_PRELAUNCH; transport log retains the exact pinning assertion. No submitted process was retried.

L056 failed before C output creation because owned NJS_native directory was absent. L058 uploads the two unchanged canonical C inputs first, creating that directory; no validation or memory limit changed.
