# Stream B function ledger evidence

The source inventory is reproduced with `python3 tools/pv-ledger/enumerate.py`.
All provider access is read-only `git show` at the full revisions in the manifest.
The three slice cohorts are intentional: existing N94906 syntax, N94915 f31/f35
constructor syntax, and N94917 allocator syntax. Function ids are not statement
ids: retain each call's cohort-local statement identity. Trait routes 1670/1686
and 38389/38321/38973 follow the installed source-derived resolvers; the TLS
callback 38964 forwards to Cell::get f18. Source-selected TLS tokens 468/469 are
named children in the current original-entry interpreter.

The enumeration is a conservative closure over complete executed function
syntax, including alternate/cleanup arms and suffixes after the current target.
It does not assert that all these arms run before OwnInit. Structured off-path
functions stop as LEAF boundaries, as the installed resolver already requires.
Native Drop and CopyNonOverlapping instructions have builtin LEAF rows, with
all individual instruction sites retained. An intrinsic catch_unwind leaf has
a documented higher-order edge to the executed callback f316.

Programs.source7 is the source-model obligation associated with slice f0;
the 16-column loop is f9, not a second invented Rust function. OwnInit is an
additional composition target, explicitly distinguished from emitted functions.
No contract is proved in this job. No host runs or Lean compiles are needed.

Rules read: /Users/dominic/ZK/AGENTS.md and pv-common.txt in full, including
all lead rulings and B-y (LOG D860), plus its r1p-common/local-lean references.
No frozen source, trust field, endpoint premise, key, or other worktree changed.
