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
maximum body and a corrected machine-checked 104.26208146248575-bit conditional
ledger. Production feasibility remains unestablished because the V8 parsed
source/scalar-check composition, legal-image hiding containment, production
wrapper stack safety, full verifier integration, and actual V8 transaction CU
measurements are open. The isolated streaming quotient probe is stack-safe at
2,176/2,112-byte frames and measures 807,012/791,539 CU; canonical parsing alone
measures 634,879 CU. The exact affine-chord coordinate-ring degree drop and
natural-basis quotient-message bridge are proved for both source interpolation
branches.

review.security_score: C
review.quality_score: B
review.ready_for_mainnet: false
review.findings:
  - severity: Critical
    category: Security
    description: Exact zero knowledge is not source-closed. A legal
      Frobenius-conjugate OOD pair disproves ambient rank 108 (actual rank 104)
      in both pair and pair-forest layouts, so universal ambient surjectivity is
      the wrong target. A focused fixture nevertheless contains all 1,022
      conservative physical directions in each of 16 mask-column images.
    fix: Prove that the complete same-statement witness image is contained in
      the mask image for every valid q22 schedule and both layouts, including
      conjugate/equal-functional cases. First translate the actual q22 row maps,
      pair-forest inventory, raw difference, and balancing helper; do not enlarge
      the mask merely to span unreachable ambient coordinates.
  - severity: Closed
    category: Correctness
    description: The corrected affine-chord quotient has exact distinct-x and
      equal-x coordinate-ring degree theorems and an actual 1024-entry
      natural-basis message representative after width-29 batching.
    fix: Consume this theorem in the remaining V8 parser/transcript source
      translation and feature-gated verifier integration.
  - severity: Critical
    category: Security
    description: The exact compiler replay now constructs a fallback-free
      partial K1.4 provider, but production parsing is still V7/q16 and Rust
      checks two scalar gamma dots rather than component-wise tuple equality.
      Lean's conservative scalar-family event is at most 2,800 gammas.
    fix: Translate a 697-QM31 V8 raw/parsed message and scalar-consistency
      classifier, compose it with the 2,800 bound across the existing replay,
      and reassemble shifted K1.2-K1.6 with source-derived Q/R resources.
  - severity: High
    category: Testing
    description: Linux reproduced the default-off V7 canonical-fixed audit
      profile at 1,153,267 CU same-page and 1,218,981 CU rollover; its proof
      bodies are exactly 320 bytes above packed V7. The isolated V8 streaming
      kernels now fit 2,176/2,112-byte frames and measure 807,012/791,539 CU;
      canonical parsing alone is 634,879 CU. The production wrapper remains
      4,736 bytes, a straightforward combined probe exhausted 1.4M CU, and no
      complete V8 transaction measurement exists.
    fix: Fuse canonical parsing with streaming quotient preparation, refactor
      the production wrapper, and integrate a complete honest V8 verifier/prover
      fixture before running same-page/rollover transaction CU, heap, CPI, SHA,
      and inversion measurements.
  - severity: Medium
    category: Testing
    description: Cross-language agreement covers local structures but not a
      complete byte-level V8 proof/transcript/verifier known-answer vector.
    fix: Generate one deterministic proof and check every challenge, OOD point,
      vector, gamma, schedule, frontier, quotient value, packed body, and final
      result in Rust and Lean.

review.last_review: 2026-09-07
review.completed_at: 2026-09-07T09:49:39Z
review.report: docs/research/v8_a100_q22_feasibility.md
