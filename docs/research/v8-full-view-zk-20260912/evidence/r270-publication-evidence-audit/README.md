# R264/R265/R270 saved evidence audit

This is a read-only audit of published evidence bundles and the promoted Lean source copies. No Lean target, extraction, or replay was run. `audit.py` independently checks every bundle checksum entry and file inventory, source identity against the promoted target and manifest hash, GNU-time status/wall/RSS/swap fields, runner resource flags, and complete saved axiom output against both the manifest and `axioms.txt`.

Results: all three bundles pass. R264 has seven complete reports (two explicitly axiom-free; five use only `propext`, `Classical.choice`, and `Quot.sound`). R265 and R270 each have two reports with those same standard foundations only. All accepted logs exit 0, report zero swaps, and match their manifests. Resource launchers record `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean flags `-j1 -M4500`.

R264's earlier `declaration-only-no-axioms.log` has no axiom reports and is incomplete for this audit. The promoted source contains seven `#print axioms` requests; acceptance is based only on the later successful `aspis-focus-1790913747557849000.log`, which contains all seven outputs and is the log named by the manifest. The audit independently verifies the seven selected raw declaration blocks against generated R263 declarations, confirms the recorded 24 transitive helper body checks after only listed adaptations, checks all recorded binding input/output hashes, and confirms the pinned R156 QM31 representation comparison. These are mechanical source-text checks, not a semantic conclusion.

R270's rejected array-rewrite draft is retained separately: `rejected/aspis-focus-1790913879265700000.log` exits 1 and contains `sorryAx`; the README identifies the failed draft. It is not the accepted target. The accepted R270 log is a separate exit-0 run.

The audit does not make a source-semantics, security, or release-boundary decision. Detailed values and paths are in `audit.json`.
