# No-prover verify injection plan — NOT RUN

Four test-only overlay files extend the accepted saved-S2 verify kit. The
production source must match accepted6dd exactly; `prepare.py --after REF` refuses
otherwise. `--stage DIR` writes only the declared test snapshot files.
`source-pins.json` records every before/after hash and complete diff.

Changes: remove prover from the old-body/test-module guards; make diagnostic-only
returned fields conditional; expose std under cfg(test); add SHA as a test-only
dev dependency; copy the actual statement_public declaration/body byte-exact into
the test module so no aspis_prover dependency is needed. All deployed-shape fields,
55 symmetric faults, success controls, digest calls, events and observer checks
remain. Production no-prover trace::value remains a no-op; the snapshot helper
returns empty values and each comparison asserts both empty. No test hook enables
recording or changes deployed arithmetic. The test explicitly rejects cfg(prover).

Two optimized native commands are pinned in source-pins.json (default/detail),
each112 cases. Neither is authorized to run until the coordinator grants its
native window after the exclusive SBF schedule. Use the byte-exact accepted
run-host.py only within6G high/8G max/swap0 scope and immutable full-input manifest.
Root stages the clean recut source plus this declared overlay and existing proof /
public fixtures. No proof generation or SBF/runtime harness is part of this kit.

After each granted run, check-run.py requires an actual rustc test invocation
whose active cfg excludes prover, no aspis_prover extern, exact expected features,
112 case lines (56Some/56None), both success controls, zero trace-value snapshots,
the112-case marker and one passed test. It rejects zero-test or missing compiler
feature evidence. This preserves historical prover-enabled results separately.

run-host.py SHA256 is
d011230e71adac99208489591e770e92744e53f9117be18060e315770866bb8c.
The existing receipt command/exit/wall/RSS/swap/revision caps are unchanged.
No compiler/native job has run for this plan.
