# Retained approaches and failures

SbfSeal-v1-tests, source 8a9c33dd39: exit1,30 methods,9 errors,0 assertion
failures,0.098049750s,32047104B peak RSS,swap0. Exact command/hashes/runtime
and log retained in v1 receipt. Ordinary temporary fixture supplied /var/folders
on macOS; /var is a symlink. open_source correctly stopped at that ancestor.
Thus these nine tests had not reached their intended positive/hardlink cases;
the two nofollow negative checks in this run did not yet isolate the intended
symlink. No implementation relaxation or Linux attribution follows. Replacement:
canonical physical ordinary temporary fixture path chosen once during test setup,
then unchanged component-nofollow implementation. Resolve is NOT used by capture
or privileged ancestry code and is NOT a race-prevention claim.

Historical immutable failures reused, not rerun: SbfClosure SDK traversal stopped
at external criterion target (never entered/copied); old userns uid_map EPERM
retained, not attributed to macOS; old setup root-owned file beneath mutable
user-owned ancestry is unsafe even with rootfd; fd3 survivor exception unsafe;
SbfResolve lexical trace not an effect/FD proof. Old 39 synthetic and 8362 metadata
checks are historical checks, not new SbfSeal or identity gates.

f29c3e0e8c historical ResourceRssGO handoff describes unstaged guard import failure;
manager's current authoritative 468 assessment supersedes it: RLIM_INFINITY
Mac/Linux mismatch failed BEFORE GO; portability repair36049 pending separately.
Both records imply no current fresh GO authority. No live 36049 files read.

Source review after successful v2 found a non-executed approach that was too weak:
postexec fstat(range(3,256)) could miss inherited descriptors >=256 after limit
lowering. Replaced with exact proc fd inventory in the literal probe, with only
EBADF entries (closed listdir inspection descriptors) discarded. Actual fd3 or
high fd remains a survivor and rejects. Other fstat errors propagate. Requires
single-threaded guest and verified private proc; both remain actual Linux gates.
No claim that lowering RLIMIT_NOFILE closes pre-existing descriptors.
