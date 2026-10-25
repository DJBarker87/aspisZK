# PORTABILITY criteria and design (before implementation)

Base: 468619b15180119560c138c83127da58ba3b4c23, assigned branch only.
All host/SSH/network/compiler/Lean/native/ELF/operational budgets remain zero.
Epoch USED1/1 and all FIVE earlier failed metadata epochs remain charged.
This is source-only; both deployed targets remain not established.

Cause: old local.inspect saves the Linux capture and calls
`host.check_limits(info['inherited_limits'])`. That function compares AS/DATA
with this process's `resource.RLIM_INFINITY` (Darwin 9223372036854775807).
Retained Linux Python wire AS/DATA are [-1,-1]. This is not finite restriction.
Old failed sources, raw capture, audits, identity mapping and seals stay intact.

Implementation plan:
1. Leave guard.check_limits and every host check/comparator unchanged: these
   validate LOCAL getrlimit values with LOCAL resource constants.
2. Add local.check_remote_linux_limits(info, expected=None), accepting only
   explicit fixed metadata platform='linux', rlim_infinity=-1 (exact int).
   Require a dict of RLIMIT_ names with two-element lists of exact ints;
   each value must be -1 or nonnegative. Require AS/DATA exactly [-1,-1].
   Optional expected comparison remains equality of the WHOLE map, including
   unlimited cells, never a finite-only subset. No caller-supplied sentinel.
3. Generated bootstrap checks exact Linux platform and Python infinity BEFORE
   Linux runtime inventory, captures the map once, checks local AS/DATA with
   existing check_limits, and reports fixed-schema platform/infinity metadata.
   All actual numeric values remain unchanged. No rlimit mutation.
4. Use the explicit validator at local inspection and before local stage
   constructs a manifest from its saved capture. No host source changes.
   Audit other local resource/platform consumers for the same confusion.
5. New PORTABILITY-only tests reproduce old rejection from immutable snapshot;
   validate retained map on Darwin without touching live limits; reject finite
   AS/DATA either side, unsupported negatives, malformed pairs/types/missing
   fields, wrong platform/infinity and whole-map mismatches. Test exact generated
   bootstrap with job imports forbidden and only Linux runtime inventory stubbed:
   on Darwin expect fail before inventory; controlled Linux fixtures exercise
   success and bad sentinel while live resource limits remain untouched.
6. Execute actual new local.inspect control flow ONLY with ssh_python stubbed,
   retained capture + new controlled metadata, OUT redirected to fresh TEMP.
   Assert charge before transport, one transport, no retry after failure or
   charge, no downstream stage/run. Never execute retained Linux runtime payload.
7. Focused tests only via existing Python receipt runner: record exact command,
   exit/wall/RSS/swap/interpreter/source/dependency pins and axioms=N/A.
   Preserve every failure. No old full test/audit replay.
8. New seal binds old source, exact source and AST diffs, unchanged module hashes,
   current revision/dirty state, test evidence and future argv (not authorized).
   Old preparation_check/identity mapping/seals are historical and will not be
   rewritten to fit the portability delta. Future copy/preparation must explicitly
   account for the delta after independent lead review and separate allocation.

Mapping justification uses retained pin-attested Linux Python capture (-1),
local Python resource constant and Darwin SDK sys/resource.h (RLIM_INFINITY
((1<<63)-1)). The bootstrap will enforce, rather than infer, Linux Python's -1
representation. No network/document download or Linux tool invocation allowed.
No security premises or trust boundaries change; metadata is checked against a
fixed known contract, never trusted as an arbitrary sentinel. Numeric policy,
environment, cgroup controls, scanner/guard lifecycle and shipped sources stay
byte-identical. Acceptance here establishes local portability regressions only.
