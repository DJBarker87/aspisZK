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
