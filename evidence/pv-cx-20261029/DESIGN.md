# Direct frozen executable extraction

Baseline 27b582ca44a9ef7c1fc341fb9bc58610d28ed7f1, branch codex/pv-cx-20261029.
No frozen bodies or manifests will be edited. Extract directly from an exact git
archive of this baseline. No reference crate, port, or replacement prover.

Use the original ProverRwFull generation chain: caller-005, then the tracked
stage3/adapt-caller.py dictionary adapter. Charon 0.1.223 SHA daad69be…;
Aeneas binary SHA 4632746d… (full pins in inherited-tool-binary-pins.json).
Historical flags are preset aeneas, MIR built, sysroot default; Aeneas
-sequential -no-progress-bar -abort-on-error -log-debug Translate -backend lean
-split-files -emit-json. Namespace/destination and entry/opacity selection change
only. Deployed features r1p-check,aspis-r1-cost-probe/ct-host-prover, release,
locked deployed dependency resolution. Extractor toolchain nightly-2026-06-01
rather than 1.94.1 per x'; retain V370/compiler cohort boundary.

Native IDs N73300–N73329, at most one scope at a time, 6G/8G/swap 0/64 tasks;
Lean 73200–73299 (audits 73297–73299), at most 60 attempts. Admission must be
allowed=true AND exit 0 immediately before scope launch. Refusals wait 180s.
Every run retains exact command, source/tool pins, exit, wall, RSS and swap.

Acceptance: main, plan::run, plan::prove remain transparent. Dependencies opaque;
prover call remains a named external boundary linked by exact carrier identity
to existing ProverRwFull, never duplicated. Inventory comes from successful
emission, not a guessed dictionary. Types/Funs must compile without template
axioms. On refusal isolate by entry and permitted flags/opacity only. If source
adaptation is required, stop and report exact diagnostic and source span.

No writer world in this task. Next EVH must use STATEFUL world semantics:
R1Z.ProverRwEntropyIteration.no_retry_then_success excludes a fixed pure entropy
dictionary for retry then success. Retain all 19 OPEN fields until bound.
D474(C) is not adopted; pin reporting spans and mark draft scope unconfirmed
unless a committed bundle can be identified. No keys are generated or executed.
