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

## Final review superseding the raw-clone implementation

The 53-case mock result and first package/source audit apply ONLY to revision
2fbed82313b0e2408017dbb401bc7ead40af846b. They do not validate the final source.
The full rejected raw-clone source bodies remain in
SbfLinux-rejected-raw-clone-sources.json. Python-level hooks after a ctypes raw
clone return are too late to satisfy the CPython continuation requirement.
The prior bullet describing that as a replacement is superseded.

Final replacement uses CPython's os.fork, whose native implementation performs
its own fork hooks. Parent remains single-threaded with default SIGCHLD and no
other reaper. A direct child remains unreaped (so its numeric PID cannot be
reused) during pidfd_open. Child blocks on a private CLOEXEC pipe before setup;
parent opens/validates own pidfd and checks signal support before sending the
fixed G byte. If pidfd acquisition fails, parent closes gate -> child gets EOF
and unconditionally _exit, then parent reaps it without numeric-PID signalling.
After release all cancellation uses retained own pidfd. No raw-clone ABI or
hand-written Python hook sequence remains. This changed source justifies the
new v3 mock run and v2 package audit; previous evidence is preserved.
