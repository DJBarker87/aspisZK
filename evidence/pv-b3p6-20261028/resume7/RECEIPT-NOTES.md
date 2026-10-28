# D414 receipt notes

- Worktree and branch were checked at entry: exact requested path, branch
  codex/pv-b3p6-20261028, head1b86d5a589e710a7c48c726c27392aa200e72223.
- IDs61500–61599 exclusively;61597–61599 reserved for final supporting audit
  targets. Native compilation scopes use separate llvm227-resume7 labels.
- Existing run.py checks its recorded cooldown and a current outer admission
  exit0 AND allowed:true before starting the capped scope, then its inner
  barrier checks admission again. Refusals were retried with the same unused
  ID after the full180-second cooldown. Final admission-audit.json checks the
  timestamps against refusal-file creation times, not just earlier snapshots.
- The initial LLVM preflight assertion failed before any admission/compiler
  because the old parts freeze included an older owned reference_terminal.rs.
  Shipped crate hashes all matched. The corrected preflight records that
  unrelated parent-source change; cargo rustc -p aspis-r1-cost-probe compiles
  the unchanged shipped package and its dependencies, not that owned body.
  This is no new owned-versus-shipped differential claim.
- Two private dependency queue controllers were intentionally stopped to test
  focused new lemmas and inspect the reached LLVM dependencies sooner. Their
  current compile child was allowed to finish and its original receipt was
  recovered before any new scope started (61527 and61553). The SSH exits255
  were consequences of stopping those controllers, not missing proof results;
  neither target was resubmitted. No compiler or other job was killed.
- Rebuilt private dependencies had no surviving objects after resume6's
  cleanup. These are missing-artifact restorations, not repeated unchanged
  release regressions. All5673 external objects were verified before the first
  compile; no shared source or object was replaced.
- Native LLVM compilation used rustc1.94.1, the deployed resolved features and
  dependency versions, release opt-level3 with overflow/debug checks off,
  jobs4 and the unchanged6G/8G/swap0/TasksMax64 scopes. It generated textual
  library LLVM; no release executable/ELF pin is claimed to be rebuilt.
- Every failed Lean source is retained beside its receipt. No failing artifact
  or sorryAx report is credited by the final axioms audit.
- Charon/Aeneas semantic uses are reclassification within existing tool trust.
  Compiler/runtime glue remains a named P boundary, never a new T field.
