PROVED a typed scanner state with two zero counters projects to q0 and is valid independently of backing array values.

Limitations: Requires zero counter provenance; actual emitted default constructor must derive those facts. No DefaultArray implementation/zero-buffer correspondence is assumed or proved. No production outer-loop refinement, source caller reachability or probabilistic security claim. Focused cached compilation only.
