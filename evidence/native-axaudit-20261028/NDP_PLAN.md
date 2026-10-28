# Strict import-wide axiom audit

Stage 1: implement a raw kernel-constant dependency traversal and an independent
module declaration-table inventory. Compile the helper alone, then exercise it
on propext before loading either release root. No existing proof is modified.

Stage 2: audit RPx_Deployed.deployed and JHx_Joint.source separately against
COPIED predecessor object forests. Inventory every axiom, exact type and module;
record actual root import membership separately from audit-tool imports. Compare
raw-body reachability with collectAxioms and each root's #print axioms. Exhaustive
visited-name files support negative reachability findings and are compressed.

Stage 3: join the inventories, validate every classification, and write the final
report and handoff. The task establishes only the logical-axiom obligation;
release-artifact, hypothesis, native-refinement and security-contract obligations
are unaffected. Retain the own cache and all attempts, including failures.

Limits: 20 Lean compiles, one 6G/8G swap-0 TasksMax-64 scope at a time,
Lean -M7000. The explicit delegation permits one lead-owned agg16 import-only
exception per root after a normal-cap import failure; its use must be recorded.
