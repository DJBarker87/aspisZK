# Source-shaped bound refinement

Run12 (exact transfer, bound33) was reviewed and stopped after1262.77s, exit-15, peak5552660480 RSS bytes, swap0. It establishes no equality/counterexample. Its scope is inactive.

The next two exact-input harnesses use25. Both records loops traverse24 levels; the owned reference traverses24 levels and8 lanes. The shipped helper traverses20 levels; arrays contain at most24 entries; Poseidon width16,4+14+4 rounds, with individual loop bounds at most16. No inverse loop is called (the fixture inverse is literal).25 includes the largest24-iteration loop plus its exit check. This retains all existing frontend/CBMC flags and all unwinding assertions: insufficient unwinding is an error, not an assumption. No source callee is stubbed and no safety check is disabled. All memory caps remain unchanged.

This changes the verification graph at every nested loop rather than repeating the conservative33-bound target unchanged. The exact-fixture generator permanently emits the refined harnesses, and --check passes. Any verification failure must be distinguished from an unwinding failure before claiming a ROW counterexample.

Run04 ten-minute review: no new compiled target or counterexample has appeared; the process is in one CBMC whole-record aggregation with the same scope cap and roughly4.5GiB memory. No cap increase is justified or requested. Continue only to the900s ceiling under the newly read ruling(i), then stop and change proof shape.

Run04 ended by worker TERM of its own timeout process at895.888s, exit-15, peak5228564480 RSS bytes, swap0. It established no result and no ROW counterexample; ended.log confirms the scope inactive. The next direct extraction reservation (charon10) refused at05:44:04 UTC, so no host scope may start until the three-minute wait is satisfied.
