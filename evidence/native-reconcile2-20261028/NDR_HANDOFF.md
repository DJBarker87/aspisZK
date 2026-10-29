# Reconciliation replay — work in progress

Target not yet established. This is a live checkpoint, not a release result.

The historical observer carrier in NDO_JGi_FinishFields.source is explicitly
restored to RPz7_PhaseIso.Phase (= FirstCaller.Phase by the already checked
NDO_PhaseIdentity.retainedCarrier). NDR_L001 passes with standard axioms only.
Two release callers explicitly apply observerToFirst none and noneToFirst;
their theorem statements are unchanged and await dependency-ordered compilation.
NDR_ADAPTATIONS.md and NDR_CHANGE_AUDIT.json record the exact before/after edits
and the 23 upstream body differences. Arbitrary non-None adaptive execution
transport is not newly proved or claimed.

NDR_PROVENANCE.json inventories all 76 historical source/object provenance gaps.
Every historical object is excluded from the statically traversed retargeted
combined closure. This does not claim recovery of historical source pins or
kernel replay of the predicted 16,061-module graph.

Chunk receipts and attempts are appended as work advances. NDR_B001–NDR_B018 passed all
2,160 modules; every printed axiom audit line has now been independently
checked to contain only propext, Classical.choice, Quot.sound. Every chunk
reports zero swap. The largest completed-chunk peak is 7,077,788 KiB RSS. One admitted 6G/8G scope,
swap 0, TasksMax 64 and one Lean -j1 -M7000 process at a time are used. Sources,
revision, commands and timing artifacts are retained per attempt. The serial
transport currently runs chunk NDR_B019 (indices 2160–2279) using NDR_build_all.py; failure
stops it. Failed chunks must be split and failed/slow modules inspected before
any replacement. No unchanged failed chunk or timed-out module is authorized
for rerun.

The new NDR_CombinedAudit source is prepared but UNCOMPILED. It imports both
roots, audits their own S2W_D189Wrappers.first/second constants and axioms, and
states the original joint witness through the headline FIp/IDa installed
configuration using NDO_InstalledIdentity.finalInstalled. The one 16 GiB
combined allowance remains unspent. NDR_agg.py verifies the three inherited
lead runner hashes immediately before admission and submission. No combined
passing result, native-code refinement, security-contract discharge or release
artifact connection is claimed yet.

Predecessor attempts: 6 single-module, 0 chunks, 0 agg16. New focused attempts:
1. Chunk budget 40; normal budget 60; agg16 budget 1. The retained host cache is
/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028 and must not
be deleted. Both predecessor caches remain read-only. No wallet or keys touched.
No push or merge.
