# Source-shaped bound refinement

Run12 (exact transfer, bound33) was reviewed and stopped after1262.77s, exit-15, peak5552660480 RSS bytes, swap0. It establishes no equality/counterexample. Its scope is inactive.

The next two exact-input harnesses use25. Both records loops traverse24 levels; the owned reference traverses24 levels and8 lanes. The shipped helper traverses20 levels; arrays contain at most24 entries; Poseidon width16,4+14+4 rounds, with individual loop bounds at most16. No inverse loop is called (the fixture inverse is literal).25 includes the largest24-iteration loop plus its exit check. This retains all existing frontend/CBMC flags and all unwinding assertions: insufficient unwinding is an error, not an assumption. No source callee is stubbed and no safety check is disabled. All memory caps remain unchanged.

This changes the verification graph at every nested loop rather than repeating the conservative33-bound target unchanged. The exact-fixture generator permanently emits the refined harnesses, and --check passes. Any verification failure must be distinguished from an unwinding failure before claiming a ROW counterexample.
