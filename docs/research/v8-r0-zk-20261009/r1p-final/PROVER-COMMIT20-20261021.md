# Prover commitment part 20 — simulator source isolation

Base `8f5d893d7`; branch `codex/cx-prover-commit20-20261021`.

Target not yet established. Work in progress: isolate the transcript/parser
translation failure, split table transport by entry, then assess the concrete
experiment and ideal WholeRunJoin against the actual source definitions.

D129 supplies the accepted three-ELF recheck for the base. No shipped source
has been changed in this stage. Concurrent-owner modules are untouched.

Host workspace reuses compiled part-19 caches. Sources start as hardlinks;
every edited source is detached before writing. Host launcher is forced to
the global Lean lock with 6G/8G/no-swap/64-task caps. Assigned attempts begin
at J8705 after checking existing receipts (last used J8704).
