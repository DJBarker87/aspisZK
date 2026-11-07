# Owned runner changes

NMK runner copied read-only into NMN, renamed owned paths and fixed compiler budget60 (reserve2 final gates). Added Stream A cwd/cgroup count before each admission; count>=2 waits180s with a wait record. Shared reservation/launcher unchanged.

The dependency-current-source validator now skips non-module share/wait records via get(module); it still requires a successful current-hash direct-import compile. This is own-script maintenance under worker-script ruling, with unchanged validation strength.

Native gate remains the inherited strict frozen source/lock/dependency/feature validator with owned prefix/path substitutions only. No cargo-kani --locked flag; metadata --locked is retained, CARGO_NET_OFFLINE=true and post-run lock identity required.

Program helper inputs are now uploaded explicitly (NMN_heap.rs/NMN_statement.rs). An indentation error in that owned client edit was detected by Python before any SSH or scope; the exact failed script is retained in NMN_PROGRAM_RUNNER_PARSE_FAILURE.txt, with a prelaunch (not Kani) ATTEMPTS row. The indentation was corrected; shared launch/admission code and validation strength were unchanged.

Sequential native batches use the UNCHANGED S2W runner in one capped scope, to avoid repeated admission gaps between tiny independent variant cases. Each actual cargo-kani invocation still gets its OWN frozen-source/graph/features/offline/post-lock validation, stdout/time/RSS/swap/command receipt, source/dependency pins and budget row. Scope-only IDs901+ have kind=batch and are not additional Kani invocations. The inner90s and outer180s limits/caps remain unchanged. A timeout retires only that shape; independent cases proceed. Budget admission counts all inner invocations, never just scopes. NMN_gate adds only a pre-invocation marker after all validation, so prelaunch failures cannot be mistaken for Kani runs. No shared launcher/reservation/monitor is edited.

K037 reached cargo-kani compilation but no verification: pinned Kani resolved a doubly-glob-imported encoder path as ambiguous (same DefId listed twice). Fully qualified encoder/auth stub targets fix the own harness input; no frozen body or semantic condition changes. The pre-invocation marker distinguishes this real cargo-kani invocation from the earlier local Python parse failure.
