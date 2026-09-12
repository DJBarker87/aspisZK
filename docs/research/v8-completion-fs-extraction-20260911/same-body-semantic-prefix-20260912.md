# Same-body semantic transcript prefix

Status: focused functional construction proved; semantic-terminal acceptance,
literal Rust refinement, and probability claims remain open.

## Result

`SameBodySemanticWire.lean` parses the selected wire once and projects both
the 697 canonical fixed values and the two 26-byte roots from that same body.
`FSLiveSemanticPrefix.lean` consumes that object in the pinned semantic order:

1. zero transcript state and the compile-time positive-transfer adapter;
2. V8 profile, authenticated-statement binding, and body-derived C1 root;
3. live bounded lambda and chi draws, then the body-derived C2 root;
4. the literal registry/helper records and live theta, ten-coordinate
   zerocheck point, and mu draws;
5. the body-derived masked claim and three-attempt nonzero eta sampler; and
6. ten literal 433-byte compact round records, each preceding its live `z`
   draw and carried-scalar update.

Parsing and every sampler failure are explicit.  The selected positive
descriptor is the verifier-derived 107-byte value from the pinned research
source; the alternative path performs no dummy oracle call.  The fixed Script
allowance is 1,800 calls/slots and includes all bounded retry paths.

`successful_run_has_same_body_wire` now returns the successful same-body parse
and its exact sequential fixed-field result.  Independent roots or a separate
field table are not constructor inputs.

## Focused replay

Base revision: `b265d6a2900447be54c65887da95754595fbc6c7`.

The two leaves were compiled separately on the Tailscale NUC using Lean
4.32.0, one job at a time, under a user systemd scope with `MemoryHigh=8G`,
`MemoryMax=9G`, `MemorySwapMax=0`, and `RuntimeMaxSec=600`.

| Target | Exit | Wall | Peak RSS | Swap | Source SHA-256 | OLean SHA-256 |
|---|---:|---:|---:|---:|---|---|
| `SameBodySemanticWire.lean` | 0 | 2.65 s | 6,554,316 KiB | 0 | `60610adccd1eff9da5f84b0b2945f96528a00c36bf3e276324de4016275ba33b` | `182743eeef21aea4db841cd4ba1c7ab0223a4fa3ad6fc877fa8d3a642f34a3ef` |
| `FSLiveSemanticPrefix.lean` | 0 | 14.18 s | 6,740,456 KiB | 0 | `7515714e9a5f3a635f5edaa3d256cb79bcab1102db3ccc90ef7dbe33e7129a56` | `a556752941bc920d996a7a6d35a9ad048ac130b64db3b3fcbb3f1c19af1d6f64` |

The printed axiom closure contains only `propext`, `Classical.choice`, and
`Quot.sound`; the literal-length declarations use fewer or no axioms.  The
private combined OLean directory reused pinned dependencies and is not a
first-party dependency rebuild.

## Exact remaining boundaries

- The Boolean profile selector must be identified with the compiled Rust cfg.
- The binding must be produced by the authenticated statement/attempt/context
  wrapper rather than supplied by an adversary.
- Authentication must prove the parsed roots equal the chronological C1/C2
  commitment-cut roots.
- The optimized Rust field/parser implementation still needs functional
  refinement.
- The selected semantic terminal must be evaluated from these challenges and
  proved equal to the carried scalar on an accepting run.
- This deterministic prefix establishes neither random-oracle freshness nor a
  soundness probability.

No wire bytes, proof-body size, verifier acceptance rule, or production code
changed.
