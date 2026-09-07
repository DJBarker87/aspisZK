# Next gate: actual image-aware relation acceptance, not query-only coverage

Continue the Aspis V8 research from 67ba3ff1 and any explicitly pinned newer
source. Preserve production, the 40,282-byte allowance, no security credit for
grinding, full-view ZK and matched full-transaction CU requirements. Read AGENTS.md;
respect focused Lean builds and resource limits. No deployment or default changes.

The attached review derives a restricted, causal ideal-game upper bound for the
T_512 obstruction and more generally EXACT polynomial quotients in W with nonzero
image residual. It does not solve arbitrary-oracle recovery. Audit the derivation
before porting it, and do not assume its conclusion as a premise.

1. TRACE THE ACTUAL GATE FIRST.
   Inspect actual V8 source and profile, not only the research transpose.
   Identify whether E1=Q[1023] and E2=b*Q[1022]-c*Q[1021] are installed as zero
   linear claims in the SAME relation sumcheck at the 1024-level, before alpha0.
   Record exact labels, challenge ordering, inputs and code locations. If absent,
   call this a proposed verifier change, not a proof-only repair. Prototype only
   in research. Do not claim a production omission from unavailable source.

2. SETTLE THE SPECIFIC FULL-DEGREE CLASS.
   Establish exact encoder/index packaging of E1=0 and E2=512*gamma^ell for
   the pre-OOD T_512 word, including legal chord and equal-x cases. In the general
   local theorem, Q, ordinary weight and scalar are fixed before fresh image
   challenge tau; require an ACTUAL nonzero image vector, not decoder membership.
   Define a causal game with an adaptive final256 chosen after alpha0 but before
   the fresh query sample. Prove the partition:
      final256=true fold -> prior false relation survives query injection;
      final256!=true fold -> at most 255 matching final-domain points.
   Use the source's shifted degree-q rho discrepancy for arbitrary prior.
   Prove fresh sequential degree-six repair counts for all four relation rounds.
   Target the derived conservative bound
      (q+2)/(k-1) + 24/k + choose(255,q)/choose(T,q)
   or a justified correction, under fully stated ideal-game assumptions. At q22
   it screens at 118.4150 bits. Do not advertise this as full V8 security.
   Do not obtain the theorem by adding its exact acceptance-error bound as an
   upstream hypothesis. The algebra, game, partition and causal counting must
   construct the conclusion.

3. KEEP THE IMPLEMENTATION SMALL.
   Check the actual four-fold image-weight expression:
      only index 3 += (alpha1*alpha2*alpha3/256) *
           (tau*alpha0 + tau^2*(b*alpha0^2-c*alpha0^3)).
   Compare with independent dense image-covector folds under current source order.
   This is an update to the carried relation weights, NOT a standalone final
   membership test. The single-fold kernel (-alpha0^3,0,0,1) is a regression for
   that false shortcut. Reuse alpha powers and base scalings. Establish parsing,
   source, transcript and ZK implications; do not infer CU from arithmetic count.

4. DO NOT DISCARD THE OTHER BRANCHES.
   Keep original, paired and high-J image-valid root-product regressions. Their
   virtual words are not globally exact low-degree polynomials; the local theorem
   cannot assume otherwise to absorb them. State explicitly how accepted,
   image-valid non-polynomial outside branches remain in the probability space.
   The next genuine global milestone remains an upper bound on their accepted
   adaptive mass, not a new fixed-target theorem or a renamed old decoder error.

5. DELIVER THE SOURCE CONNECTION OR THE EXACT MISSING LINK.
   Produce a source/check map, focused Lean proof and axiom record where feasible,
   any research-only gate diff and complete byte implications, plus exact tests.
   Either show the concrete source rejects the obstruction except through named
   fresh-challenge error events, or specify what actual check/order is missing.
   Report positive local progress without marking the full q22 certificate green.
   Do not start heavy full-prover/SBF runs until the cryptographic and source
   predecessor is identified; no unapproved remote job. No repeated unchanged
   rank/formal workloads. No extra proof budget assumed.
