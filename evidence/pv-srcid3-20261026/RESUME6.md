# Resume allocation 6

Base 92d3db0b2f; research pinned c16e7e7895b7383b7f285b8bd964727e34777e4b.
Authorized 100 Lean attempts and 4 Kani runs. Env-J IDs 37100–37399 only;
never reused. Last three charged Lean attempts reserved for the full audit.
The shared host restoration flag and rulings (a)–(g) were read before host work.

37100: resource reservation refusal, no source replacement and no compile.
Reservation at 2026-10-27T00:09:24Z would total 60,532,195,328 bytes versus
59,055,800,320 safe limit. Wait three minutes and use 37101 or next unused ID.

The source graph contains 839 project modules and 193 external import roots.
The exact R1NaturalProjection downstream replacement closure alone has 163
members, including FinalAudit. This allocation cannot rebuild that whole
closure and run the three reserved final attempts even if every compile passes.
No clean gate is claimed from the previous 579-report kernel audit.

All shared replacements retain pre-replacement source/object snapshots under
codex-pv-srcid-20261026/snapshots/resume6-ID. Rebuilt dependents use fresh
import-object fingerprints. The launcher was inspected without modification:
it currently executes TasksMax=64 (within the accepted limits), -M7000,
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0. Its run2.py prepends joint objects
to LEAN_PATH, which agrees with the closure inventory's resolution precedence.

## Merge repair compile failure

37101: allocated but stopped by the local mandatory-wait guard (86.97 s remained);
no host scope and no charge. The client then waited 180 s and used 37102.
37102: R1NaturalProjection exact research source sha 41db583f…; exit 1,
wall 1.41 s, peak RSS 2,729,920 KiB, swaps 0, branch revision 79e2278e2e.
Eight axiom reports were printed; five include rejected sorryAx arising from
unsolved goals at source lines 28 and 58. No sorry/admit construct was added.
The unchanged failed source will not be rerun. No source-level edit to this
protected soundness module is authorized or made. The original object remains
retained in the pre-replacement snapshot, not certified as research HEAD.

The recursive host package-source graph enumerates 6,326 objects, none missing,
and 103 unavailable source copies. Their exact names and graph gaps are in
resume6-package-closure.json. The project-only receipt scan hash-links 759/839
objects; 80 exact gaps remain (some branch-only). This does not upgrade package
copies to source/object compilation provenance. MERGE-GATE.md lists every
enumerated imported object and fails closed on each unproved association.

Gate work is blocked by a protected source proof failure, not a ROW
counterexample or a resource refusal. Continue independent pure-source work
with the remaining 99 attempts; preserve three for the final complete audit.
