# Literal query-context evidence

This target proves two model-level coherence facts: the current row challenge is not consumed by matching-data reads, and `beforeRho (P.ext m c)` equals `atQuery P m`. It says nothing about accepted execution, source correspondence, or security closure.

Attempt `a` failed because `InitialWalk.Bytes` and `current_readAt_challenge_independent` were not in scope; its two emitted declaration reports include `sorryAx`, and the exact attempt is retained. Attempt `b` is green: 1.84 s, 3,591,400 KiB peak RSS, zero swap, and three standard axiom reports. The run used a 4G high / 6G max / zero-swap cgroup under Lean 4.32.0. See `source-manifest.json` for exact snapshots, imports, objects, and runner pins.
