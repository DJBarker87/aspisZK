# D518 resume gate

Worktree `/Users/dominic/ZK/.worktrees/pv-cx`, branch `codex/pv-cx-20261029`,
resume revision `570c0008098b8cc23d16d86f9edb0c2a41b0e118`.
Frozen executable input remains N73309 at baseline `27b582ca44a9ef7c1fc341fb9bc58610d28ed7f1`.
No edit under crates, programs, or tools/r1-cost-probe is authorized.

Identity order: original b59d5188 plus retained accepted-extensions.patch,
verified against original source manifest; capped static rebuild; compare
4632746d binary hash; if different, reproduce caller-005 (the input to the
tracked ProverRwFull adapter) and two additional independently pinned LLBC
extractions using their exact historical flags. Independently test backup
562e1f51 with the same three comparisons. Neither candidate is adopted until
its gate passes. No passing candidate means STOP as an owner item, per the
explicit resume instruction and ae1. This supersedes the inherited generic
instruction to spend the entire budget on alternate proof routes.

Budgets: at most 40 Lean attempts in 73250–73296, audit IDs 73297–73299;
20 native scopes N73330–N73349; zero Kani. Each native build/extraction has
6 GiB high, 8 GiB max, zero swap, 64 tasks; at most one scope at a time.
Both admission exit status and allowed:true are required before launch and
at release of the owned container barrier. No other job directory is written.

After identity: run the accepted translator on retained N73309, compile Types
then Funs using standard axioms only, and import the existing ProverRwFull
entry for the declaration-identity link. No prover re-extraction for the new
client; caller-005 regeneration serves only the mandated translator test.
No writer world, no new trust field, and no privacy-premise claim from an
inventory alone. All 19 OPEN runtime fields stay open until actually bound.
