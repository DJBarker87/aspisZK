# Live selected middle-to-query transcript splice

Status: **focused deterministic Lean milestone; not a Fiat–Shamir law or
literal Rust refinement**.

`lean/FSLiveSelectedMiddleQueryRho.lean` joins the existing chronological
source/OOD/gamma script to the selected relation middle and the already checked
final256/q22/rho suffix.  In one `Script`, the order is now structural:

1. the source prefix fixes C1, constructs C2 at its permitted boundary, absorbs
   both OOD rows, and samples nonzero gamma;
2. fixed field 358 is absorbed as the inactive claim;
3. nonzero kappa is sampled;
4. the verifier-derived compact functional description and ordinary claim are
   absorbed, followed by the image-profile framing;
5. nonzero tau is sampled;
6. response 0 (fixed fields 417--422) is absorbed before alpha0;
7. alpha0 is sampled after its nonce;
8. final256 is absorbed and the q22 schedule is fixed before nonzero rho.

All bounded-retry failures and source/callback aborts remain explicit.  The
theorem `successful_source_middle_components` decomposes any successful
composite run into the successful source/OOD/gamma run and the exact middle
continuation from the returned digest and oracle state.  `literal_body_ranges`
pins the body offsets used by this slice.

The remaining deterministic boundary is intentionally visible as
`FunctionalProducer`: the pinned Rust `structured_weights::prepare` calculation
of the compact public functional description and ordinary claim has not yet
been refined to this Lean producer.  This leaf therefore does not establish
that the transcript inputs are the literal Rust outputs, challenge freshness,
or a probability theorem.

## Focused evidence

- Base revision: `abd6e22352d5db192fe015e43f4f55d2e0091439`.
- Lean: pinned 4.32.0 environment on the NUC build workspace.
- Source SHA-256:
  `9040eaf3994abe8fa42c761396d337a7687f3fe0caf22f1015170231f923f501`.
- Olean SHA-256:
  `1d45c0d49cf940e20066e72429b8a911c603e694653c816ce91a1a9a8c0084d3`.
- Exit: 0; wall: 6.20 seconds; peak RSS: 6,595,888 KiB; swap: 0.
- Cgroup: `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`,
  `RuntimeMaxSec=300`.
- Printed axioms: `propext`, `Classical.choice`, `Quot.sound` only.

The body cap remains 40,282 bytes and no grinding credit is introduced.
