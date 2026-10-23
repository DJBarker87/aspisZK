# Retained circle wrapper: canonical output coordinates

Proved: every successful call of the retained emitted `sampler.circle_sample`, on either row, returns two canonically encoded coordinates. Sampling canonicality, the secure mapper's canonical output, and both explicit fallback branches are reused from existing proofs. The new symbolic fallback adapter lemma prevents evaluation of closed fallback constants.

This lemma concerns the existing emitted wrapper with its concrete Lean callee adapters. It does not prove that those adapters refine the current Rust callees or that the current `circle_validated`/Prepared.z execution reaches these exact calls. These obligations remain open; no complete S9 or security claim is made.

The focused v3 check passed with only standard axioms, zero process swaps and the exact resource/source/object receipts included here. Retained predecessors show an environment-only missing namespace object and a source error involving missing fallback namespace and concrete reduction. No failed attempt is counted as a pass, no resource option was raised, and no compiled artifact is included.

The complete available `AspisV8R19` namespace owner is a union of cached profile roots preserving their original per-module first-owner precedence. Its selected object hashes, all conflicting alternatives, and one unavailable legacy broken symlink are recorded in `proof/namespace-owner-manifest.json`. This is cache reuse, not a full release dependency replay. The exact source input hash and focused preflight/profile are recorded separately.

Run `python3 check_packet.py` for immutable-source/evidence, focused exit/resource/axiom and namespace-owner checks. It does not invoke Lean.
