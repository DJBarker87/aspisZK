# R425 fixture-run saved evidence audit

The audit reads the saved fixture build and execution receipts, GNU-time files, Docker inspections, source snapshots, reviewed fixture sources, and retained v1/v2 execution preflight logs. Running `python3 audit_saved_fixture_runs.py` performs no build or fixture execution; it writes only the derived audit and metrics JSON here.

The first execution preflight (`fixture-execution-preflight-v1.log`) aborted while looking for the optional postbuild executable sidecar, before creating an execution audit directory or invoking the fixture. The reviewed v2 script used the already-saved executable hash in the build result, checked it against the actual executable before invocation, and preserved the original raw output. The audit classifies v1 as a preflight failure, not a fixture failure. Native OCaml fixture checks have no Lean axiom report.
