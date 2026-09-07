# Build context

Project: Aspis V8-A100 direct-q22 transparent-proof feasibility research for
the Solana verifier and Pool one-transaction settlement path.

Architecture: the production V7 verifier uses 26 M31 C1 columns, three QM31
C2 columns, four openings per queried fibre, truncated SHA-256 Merkle roots,
and a first-cap-203 q16 candidate search. The isolated V8 research modules add
a direct q22 schedule and two component-wise pre-gamma OOD vectors, deriving
an affine-chord DEEP quotient from the existing authenticated openings without
an additional Merkle tree. The V8 modules are not reachable from a deployed
instruction.

Current result: q22 with a 26-byte digest and two OOD points has a 39,934-byte
maximum body and a machine-checked 104.26666237024358-bit conditional ledger.
Production feasibility remains unestablished because the universal hiding
theorem, restoration-wide source replay, source translation/integration, and
actual V8 SBF/Pool CU measurements are open. The exact affine-chord
coordinate-ring degree drop and natural-basis quotient-message bridge are now
proved for both source interpolation branches.

review.security_score: C
review.quality_score: B
review.ready_for_mainnet: false
review.findings:
  - severity: Critical
    category: Security
    description: Exact zero knowledge is not proved for every legal q22
      schedule and distinct secure OOD pair; only concrete pair and pair-forest
      nonzero-minor witnesses exist.
    fix: Prove universal surjectivity of the complete M31 leakage map, including
      equality cases, or retain an explicit counterexample and enlarge the mask
      to the proved minimum before making the profile reachable.
  - severity: Closed
    category: Correctness
    description: The corrected affine-chord quotient has exact distinct-x and
      equal-x coordinate-ring degree theorems and an actual 1024-entry
      natural-basis message representative after width-29 batching.
    fix: Consume this theorem in the remaining V8 parser/transcript source
      translation and feature-gated verifier integration.
  - severity: Critical
    category: Security
    description: The degree-28 gamma result is conditional on a restoration-wide
      K1.4 prefix-replay provider that the exact compiler does not yet construct.
    fix: Construct ExactCompilerPreGammaTupleObligation from the paused compiler
      for fresh, cached, and advance continuations and reassemble the shifted
      K1.2-K1.6 event theorem with source-derived Q/R resources.
  - severity: High
    category: Testing
    description: V8 has no feature-gated SBF instruction, Pool integration, or
      actual verifier/same-page/rollover CU measurements.
    fix: Add a research-only instruction preserving V7 dispatch, build on a
      capped Linux x86_64 host, and run typical and maximum-frontier strict-work
      transactions with CU, stack, heap, CPI, SHA, and inversion counters.
  - severity: Medium
    category: Testing
    description: Cross-language agreement covers local structures but not a
      complete byte-level V8 proof/transcript/verifier known-answer vector.
    fix: Generate one deterministic proof and check every challenge, OOD point,
      vector, gamma, schedule, frontier, quotient value, packed body, and final
      result in Rust and Lean.

review.last_review: 2026-09-07
review.report: docs/research/v8_a100_q22_feasibility.md
