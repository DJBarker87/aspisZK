# Retained failures and source review

* Initial repository file search assumed tools/evidence present in sparse working
  tree; rg failed. Immutable `git ls-tree` and `git show` supplied the exact
  released SbfSeal source without accessing any other worktree.
* Historical common-file LOG.md and build-integration directory are absent in
  this checkout. No historical proof or build instruction was used as authority.
* Official primary fetch for arch/x86/include/uapi/asm/resource.h returned 404.
  Previously fetched headers were retained. Generic resource header is pinned;
  source syscall prototypes, generic signal/fcntl and syscall table cover used
  ABI. No install, clone or host lookup followed the 404.
* First mock run: 42 cases, exit 1, one mock fixture omitted integer O_RDONLY /
  O_CLOEXEC, causing TypeError before the namespace check. Log/receipt and full
  initial source bodies are retained in tests-v1 and failed-v1-sources.json.
  Fix: provide actual integer constants to that fake. Not a kernel failure.
* First checked runner command supplied malformed revision argument
  `0a6996ecdd00000000000000000000000000000000`; assertion rejected it before
  importing/running tests (exit 1). Correct actual revision was then supplied.
* v2: 50 cases pass. Subsequent source review added forced _exit even if child
  gate cleanup fails, parent ownership cleanup covering close failure, native
  effect guards in test harness, and dedicated tests. Final rerun is justified
  by those source changes, not an unchanged regression.
* Rejected implementation shape: raw clone3 without Python fork hooks/GIL
  preservation. Replaced before final validation with typed PyDLL clone3 plus
  PyOS_BeforeFork/AfterFork_Parent/AfterFork_Child, pinned Python documentation.
* Retained limitation: SIGKILL and wait rely on actual kernel behavior. The
  source checks own pidfd signal support before releasing a child gate; it does
  not prove an LSM cannot distinguish signal 0 from SIGKILL. Actual cancellation,
  CPython fork behavior, syscall errno handling, D-state/reaping and parent death
  behavior need separately authorized finite runtime tests. No bounded kernel
  completion guarantee is claimed, and no privileged entrypoint is enabled.
