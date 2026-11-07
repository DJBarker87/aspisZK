# Owned controller changes

NML_NHR_stage.py is the byte-identical pinned NHR_stage.py. NML_extract.py supplies recovered historical command arrays through its options API, preserving all frozen graph/source/lock, tool and opacity checks. It additionally verifies exact standalone reference source and manifest hashes before and after every run; it writes only in the owned workspace. The manifest literal is recovered from the producing extraction script via AST, never executed. Inputs embedded in LLBC are accepted only at the exact hash named by the producing receipt.

NML_run.py is an owned NMH client adaptation. It adds read-only Stream A scope counts, mandatory recorded three-minute waits at >=2, and the 40 GB/30 GB disk checks. It requires reservation exit0 AND allowed:true, retains the unchanged SInt2 launcher, and serializes all submissions. No shared infrastructure was modified. Reference LLBC is transferred compressed with an uncompressed SHA256 sidecar. No timeout/cap is raised.

Local discovery repair: pin-output hash values may be nested dictionaries; recursive hash collection replaced an invalid set(values()) call before any compiler launch. Historical stdout logs combine an initial pin object and a separate Aeneas argv array; both are parsed without executing logged code. Discovery now includes exact embedded LLBC file contents and archived Cargo package/lib paths. These are input-recovery changes, not normalization of emission bytes.

Only whole-byte identity or NHR discriminant metadata removal establishes reproduction. Namespaces, imports, parameters and checked/wrapping arithmetic remain visible. Any comparison without a compiled equality or semantic witness stays UNCLASSIFIED. The sole inherited reproduced blob retains NMH's original receipt rather than spending an unchanged replay.

Archived full-package extension: Cargo package/lib paths in the producing packet are recorded with Git blobs, even where full configuration is absent. Executable additions require the recorded command output LLBC name, exact embedded source SHA256, and matching start/include/opaque options. Original package files are retained. A historical --locked command with an unarchived lock may fail; no lock or flag is silently fabricated or relaxed.

Receipt-context repair before any submission: source revision/dirty state is refreshed after admission waits, immediately before uploading exact source snapshots. The initial local share waiter was terminated with no admission or submitted scope and restarted; zero tool charge.

After E001, owned tool-receipt context is clarified: source_revision is the actual evidence snapshot revision; frozen_validation_revision separately labels NHR graph validation. E001 keeps its historical tool receipts and an explicit NML_E001_TOOL_CONTEXT_ERRATUM.json; exact archived source hashes and launcher source revision were already recorded. No rerun or verdict change.
