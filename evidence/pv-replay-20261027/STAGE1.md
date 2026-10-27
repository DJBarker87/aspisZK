# Private headline dry replay: plan

Pinned research: b90540e01c10a102535dcc0c0b0c50fb18880e0f. Branch base cc82f1f8677e62fde0a4fad75fe09eb48db8e8d6. No proof-source edits; unrelated staged C3-BIN edit retained untouched.

672 project modules, 121 direct external import names, no unresolved source names. Both requested roots are covered; V2 is an ancestor of DeployedReal. EJR selected/resolved source-path authority takes precedence, then EJR/EJS additions, then canonical privacy namespace for names absent from the rebuild record. Each source is read at the pinned research revision. Historical blob resolutions remain in replay-plan.json for comparison. No grep-based variant substitution.

replay-plan.tsv records dependency-first order, module, repository path, SHA256 and recursive source/import fingerprint. Compile/reuse receipts additionally record actual dependency-object fingerprints; these cannot be known for newly compiled descendants before their ancestors compile.

Host private root: /home/dombarker/project-offloads/codex-pv-replay-20261027. Attempts 28000–29999, at most 600 compiles, one scope at a time, 6G/8G/swap0/tasks64, Lean -M7000. External toolchain/manifest objects retained; Mathlib/Aeneas never rebuilt. Shared sources/objects never written. No Kani. This checks coherence only and removes no premises; target not yet established.
