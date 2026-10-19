# Arithmetic savings worker, 2026-10-19

The user tightened the target during this run: both transactions must be below
1.2M CU on all six saved fixtures. Protocol bytes and challenge scheduling remain
frozen. The first measured candidate is retained: stage 1 saves 34,201–34,243 CU;
settlement is unchanged. See candidate1/SUMMARY.json, per-run receipts, strict
stack audit and pending extracted-declaration re-pin inventory.

The native injection failure is preserved. Its old-side test hook was omitted
while adapting the harness to the gamma-output API; restoring that hook makes
all existing emitted JSON/event records match the accepted baseline exactly.
The ordered digest trace is compared as an ordered list. Only the auxiliary
repeated-input histogram is sorted (its HashMap iteration order is nondeterministic).

Hygiene: the five requested soundness roots resolve to 718 modules and 92 library
identities, with zero unresolved modules, alias collisions, differing-source
conflicts or cycles. Library object presence is not asserted by this local source
check; no Lean compilation was started. Promoted sources retain exact bytes.
Canonical split support owners are pinned explicitly; older bodies remain in Git.

No ELF or .so is committed. Runtime task/key directories remain on the NUC.
