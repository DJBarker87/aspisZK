# Repair review index

Source revision: 6ccb0487d0508512efe5de6321db9533ccd70da5. Entry base:
d39aa80a9aa0a87bf9216f5e7a08cd952b58c784. Preregistration commit f4c5edd3b1.

The exact before/after source/function statements are in
SbfFinite-entry-repair-statements.json; installer diff is
SbfFinite-entry-repair-delta.patch.txt. The internal structured result is retained;
the dormant entry now calls fixed_install_entry() -> int, publishes exactly one
fixed bounded installation-only receipt, and returns 0. Exceptions propagate.
Every public entry still raises before imports. No actual installation occurred.

New validation:

- tests-attempt11: 34 methods, exit0, 1.031637792s, self197820416B,
  serial Git child4325376B, conservative sum202145792B, swaps0/0.
- final-check3: 279 source/pin/import checks, exit0, 0.216524542s,
  self52199424B, serial Git child5898240B, sum58097664B, swaps0/0.
- entry-repair-validation1: two byte-identical regenerations plus the above,
  exit0, 1.687676500s, self22478848B, serial child197820416B,
  sum220299264B, swaps0/0. Child receipts separately report nested Git peaks;
  their conservative inclusive bound with the parent is224624640B.
- entry-repair-HANDOFF: 159 focused complete-function/delta/unchanged-source
  checks, exit0, 0.524600500s, self30523392B, serial Git child103596032B,
  sum134119424B, swaps0/0.

All concurrent aggregate peaks are UNOBSERVED; sums are conservative peak sums,
not exact aggregate measurements. Axioms=N/A for every check: no theorem/native
or security validation. Exact commands, interpreter/source/dependency hashes and
revision are in receipts. The final evidence index additionally hashes the
checker source, all retained reports and all current own tools.

Retained failures: attempt9 passed3 methods then aborted at the512MiB peak-sum
assertion before serializing exact RSS/swap/wall. Its sources/log and missing-
measurement limitation remain. Mock source buffers now share by size and prior
mock cycles are collected between subcases; cap unchanged. Focused attempt10
passed. close-failed1 compared whole class text against a per-method report map;
its exact failing source/error remain. Corrected method-granularity checker
passed159 checks. Neither failure was retried unchanged. No full frozen replay.

Historical acquisition, immutable lineage/policy and independent lead reviews
are reused source evidence, not a new identity gate. The original30 tests were
retained in the changed suite; unchanged package/core/root-entry/user-entry,
policy, captured guest mapping and OPERATIONAL_PIN=() were independently checked.
Old regenerated reports are preserved byte-for-byte under entry-repair-before.

Missing limits data is exactly the target interpreter's entire sorted RLIMIT_*
name set, each [soft,hard], for collector/helper. AS and DATA must match its
RLIM_INFINITY pair. The exact finite operational schema and every host/role/
map/env/limit/scope field are recorded in SbfFinite_REVIEW.md; no actual values
were acquired or fabricated. Next deliverable: separately reviewed finite
operational source/data pins and authenticated administrative publication, then
distinct authority/budgets for actual work. No current permission request.

Both security targets NOT ESTABLISHED. Root/kernel/CPython/native/bootstrap,
LSM/PDEATHSIG/cleanup/D-state, SDK/runtime/extraction/refinement, artifact binding
and cryptographic/adaptive joins remain open. All actual host/SSH/network/root/
namespace/native/probe/install/compiler/Lean/Rust/Cargo/Kani/extraction/backend/
ELF budgets remain0. No shipped source/protocol/model/trust/keys/RPC changed.
Stop for lead review; no merge or push.
