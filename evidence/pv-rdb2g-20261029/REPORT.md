# RDB2G — D440 exact-environment replay

Replay in progress. V256/V257 remain SUSPENDED until every required unchanged consumer and audit passes. V231 is unchanged: software path proved; SHA-NI path conditional on `R1Z.PV_RDB2F_ShaNi.SHA_NI_IntrinsicsSemantics`, pending owner item 3. Privacy target not yet established.

Exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-rdb2e`; branch `codex/pv-rdb2g-20261029`; base `0da960687bf9f66694b2fdb1fc2bd30f72586996`. All changes are replay orchestration and evidence under this directory; no Lean, Rust, production source or existing tool source edits. No new proofs, Kani, extraction or native regression.

The original environment is `plan.json:environment`, byte-equal as JSON to the original rdb2e env-J environment. Its literal LEAN_PATH begins `/home/dombarker/project-offloads/codex-pv-rdb2e-20261029/lean-objects`; all external paths and toolchain values are retained. The unchanged standing run2.py prepends that same object directory, exactly as it did in the original invocation. Both the recorded environment and effective duplicated prefix are explicit in preflight.json. Source files remain at the unchanged rdb2f source root.

Preflight checked all 178 pinned source blobs locally and the host source files, all 5,673 external object hashes, ID collisions and available cache hashes. The transitive affected set contains 49 modules including 3 audits. Prior cleanup removed another 39 required prerequisites: the complete unchanged audits require 88 attempts. Budget clarification requested before exceeding 40. Ninety unaffected canonical objects were hash-verified and copied with their available companions to the explicitly authorized original prefix. No affected historical object was staged.

Each compile uses successful same-shell admission and the standing in-scope barrier, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000, one module and one scope at a time. Raw target, admissions, output, wall, RSS, swap, source blob/revision and axioms output are retained per attempt.
