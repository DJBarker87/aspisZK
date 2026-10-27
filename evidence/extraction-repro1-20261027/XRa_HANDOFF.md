# XRa handoff: toolchain recovered, release association incomplete

**D188-P remains open. Target not yet established.** This job stops at the conservative six-invocation Charon/Aeneas budget, counting the two version probes. Four invocations performed extraction work. Lean 0/100; Kani 0/0. No new Lean module, theorem, equality proof or axioms claim exists.

Worktree: `/Users/dominic/ZK/.worktrees/cx-extraction-repro1`. Actual branch: `codex/cx-extraction-repro1-20261027` (the prompt named the 20261026 suffix; no branch switch or other-worktree write occurred). Local commits: `dcf97f5fa3` preflight; `23b8c29f16` toolchain recovery/historical reproduction; `1bce0adfa7` partial release replay/budget stop. No push or merge.

Established:

- Exact Charon cb50ff16b9f1066b8a97dc06da704de2da2fa41c and driver rebuilds reproduce the recorded executable hashes `daad69bea…` / `efdbe5b86…`.
- The historical Aeneas recipe has conflicting provenance: its “patched tree” pin `5a843e70…` identifies the base source and builds a translator that fails the retained historical LLBC. Applying the retained patch produces source-only tree `3be6820e…`, matching ALL 38 post-patch file hashes in the archived extended-tool audit, with no other source change. See **XRa_PIN.md** and **XRa_verified_extended_source.json**.
- That exact audited source rebuilds as executable `c0cf4fcc…`, not the historical `4632746d…` executable hash. Its historical replay reproduces Types, Funs, external template and translation JSON byte for byte. This is a bounded historical-input reproducibility result, not proof of release association.
- The borrowed frozen release snapshot matches all 7,978 manifest hashes before and after extraction. The recorded re-export root `verifier::tx1` yields an empty LLBC despite exit 0; it is excluded. Resolving the release re-export to **verifier::candidate::tx1** yields a nonempty LLBC: 533 functions, 104 types, `has_errors=false`, 8,946,989 bytes, SHA-256 `0814e4ec3481bef7fcca9a806ff24c868fdaeae3ed127b1e11a73973077510ba`. Actual root is Fun 0 in XRa_HostArtifacts.json.

Not established: fresh release Types/Funs; fresh-vs-cohort or fresh-vs-historical declaration/byte diffs; classifications of the eight changed cuts; class-(b) Lean equalities; either requested final association verdict. Source mismatch or movement alone is not reported as proved semantic inequality. **Do not mark the cohort producer equal to release extraction.**

Next concrete deliverable: run the exact pending Aeneas command in **XRa_NEXT_AENEAS.json**, with a renewed invocation budget and the existing reservation barrier/capped scope. The binary, LLBC and pinned sources remain in `/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027`; hashes/paths are in XRa_HostArtifacts.json. No toolchain rebuild is needed. Then complete XRa_Diff.md, the eight-cut classification, XRa_Association.lean where justified, and the final provenance verdict.

All 17 host jobs have source/command/revision/exit/wall/RSS/swap/actual-cap receipts; XRa_AttemptSummary.json and XRa_Verification.json audit them. One admitted scope at a time, 6G high/8G max/Swap0/Tasks64; optimized Rust; no cap increase, timeout or memory kill. Task-owned Cargo/Dune/opam/library/ephemeral-Git caches were removed after preserving the hashed tools and LLBC. No binaries, objects or tarballs are committed. Raw logs and patch bytes retain original whitespace for hash integrity.

Before/after: AspisR1.Rc10_Top.deployed source is identical, captured in both statement snapshots. No binder, carrier, conclusion, failure event, game clause or trust boundary changes. Ledger method preserves quantified atomic families/shared witnesses/T-P-G-C classes and deduplicates existing aliases, including L185=L159: **removed/added/changed 0/0/0; delta T0/P0/G0/C0**. No new absolute recount or joint security-game non-vacuity witness. Nonempty extraction roots do not establish theorem non-vacuity. `#print axioms`: N/A, no new theorem.

No shipped file, session A worktree/candidate, other worker prefix, ledger, contract, wallet or key changed. No ELF rebuild trigger occurred; inherited ELF pins were not newly reproduced. Only the assigned evidence directory changed.
