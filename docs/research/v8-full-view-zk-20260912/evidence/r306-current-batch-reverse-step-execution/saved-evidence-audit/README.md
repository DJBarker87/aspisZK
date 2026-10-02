# R305/R306 published evidence consistency audit

Read-only audit of the published saved evidence under `docs/research/v8-full-view-zk-20260912/evidence/`. No Lean target was compiled and no tracked file was changed. Run `python3 audit_saved_evidence.py` to reproduce the mechanical hash, log, axiom, source-block, and scope checks.

Both outer SHA-256 manifests cover every file in their evidence bundle other than the manifest file itself; no listed file is missing or hash-mismatched, and there are no unlisted files. Published source copies match the target Lean files. R305's four generated declaration blocks match the saved R292 Funs source block-for-block. Logs and `axioms.txt` agree exactly after whitespace normalization: R305 has four reports and R306 six, all limited to `propext`, `Classical.choice`, and `Quot.sound`. Recorded exit status, wall time, child peak RSS, swaps, Lean version, and cgroup/Lean flags agree with the successful logs and launch scripts.

The preserved rejected history is present: R305's earlier namespace-scaffold attempt records the missing `open Aeneas` error and `sorryAx`; all three rejected R306 drafts and logs are present and their logs expose `sorryAx`. They are separate from the successful artifacts.

The R306 boundary is appropriately limited to the selected reverse-body cases with explicit selected-read and output-index premises. It does not establish caller invariants, the batch zero guard, full chronology, or Rust standard-library correspondence. Neither note claims a security result.

One stale annotation remains inside the copied R305 precompile audit: `raw-adapter-audit/binding-audit.json` still says the source is unverified and its axiom commands have not run. The successful R305 log and four matching reports in the same published bundle supersede that historical staging status. Also, `raw-adapter-audit/SHA256SUMS` preserves its original `.r21-scratch/...` path names; use the enclosing evidence bundle's `SHA256SUMS.json` for a self-contained bundle check. These are documentation/packaging caveats, not successful-log or hash failures.
