# Gate (a) method

Source snapshot: 2910da23a3b4a3f780611728d3af122457bbef85, archived directly from this
worktree commit. No shared source tree was written. Expected time: optimized SBF
compilation and diagnostic emission. One capped scope at a time. Launcher:
`tools/pv-runjoin13-20261027/build.py`, adapted from
`git show codex/pv-rebase-20261026:tools/pv-rebase-20261026/build.py`.
The rebase design and lowering2 method were read via git show.
Private host root: /home/dombarker/project-offloads/codex-pv-runjoin-20261026/gate13.
Private target copies reuse the rebase caches; no shared cache is modified.
Every Rust source is touched before each fresh build, following the precedent.
Features, optimization flags, tools and caps are unchanged from that method.

The first devnet orchestration exited 1 before any scope/compilation because
codex-cx-pin-20261020/r1-devnet.template.json no longer exists. Its reservation
was admitted and retained. Replacement invocation uses the exact two public
program IDs recovered from the rebase branch's committed candidate/build-devnet/
command.json (devnet-environment-precedent.json). This is an input-file recovery,
not a tool/launcher or source repair; no shared infrastructure was changed.

Generated artifact keys are retained securely on the private host at mode 0600.
Never delete them as build-cache cleanup. No wallet balance/authority or refund
claim is made; no chain transactions were performed.
