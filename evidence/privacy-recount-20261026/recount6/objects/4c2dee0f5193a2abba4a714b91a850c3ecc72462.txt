# Extracted higher-order boundary finding

`PV_RE_OpaqueHashBoundary.op84_can_catch` and
`op84_can_suppress_divergence` are kernel checked in attempt 37322.
They instantiate the actual `ProverRwFull.ExternalFuns.op84` interface,
aliased as `aspis_core.r0.merkle.leaf`, with an implementation that calls the
supplied hash, matches its outer Result, and returns `.ok fallback` after
`.fail e` or `.div`. All other dictionary fields are preserved.

Locations: `ProverRwFullExternalFuns.lean:160` (op84 signature) and `:897`
(alias), under `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/`.
`opaque-higher-order-boundaries.json` lists the source call and five other
higher-order interfaces (op5, op11, op12, op119, op257), with their occurrences.
The op84 implementation body is absent from this extraction: it is a dictionary
field. No forwarding lemma can follow from this interface alone. The separate
source-context certificates forward failure of the **whole op84 call**; they
do not forward failure of a hash invocation inside op84.

This is a checked countermodel to unconditional forwarding through the
extracted opaque interface. It is NOT a counterexample to native/shipped R1:
the constructed dictionary is not claimed to satisfy the native associations,
and no native admitted input or selected native dictionary is instantiated.
Consequently the shipped-source counterexample stop condition is not met.

The native Rust `crates/aspis-core/src/r0/merkle.rs:17` body calls the hash
without an explicit Result recursor. That read-only source observation does
not supply an extracted boundary lemma or establish full native error/effect
fidelity. It is not promoted to such a law here. No mutation or new T field.

Steps 2–5 remain behind step 1's full coverage/composition proof. In particular,
this finding neither excludes a fixture callback nor proves a minimal S.
