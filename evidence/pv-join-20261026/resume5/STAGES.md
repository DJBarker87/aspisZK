# pv-join5 resume

Base 8eba145a71. Read pv-common, rulings (a)-(g), restored flag, root security/proof discipline, D42-D68 and resume4 final report. D234 supersedes the former stop: retain the raw noncanonical Horner disagreement without treating it as a row refutation. No shipped code changes.

Budget: 95 actual Lean invocations, last three for combined audit; IDs 38000-38299 never reused. Six Kani runs available. Host scopes sequential, standard caps and unchanged shared launcher. No local Lean.

Stage 1: direct extraction of shipped evaluate_state_only_polynomial via an importing proof-tool crate. Source hashes and extractor output recorded. ProverRw21ModelInstance absent at initial branch check; early ProverRw21Op223Source present.

Direct extraction results: Charon built/optimized succeeds. Aeneas rejects unused compiler-generated FnOnce Drop bodies; opacity narrowed only to these unused methods removes that preflight failure, but full source still fails in InterpReduceCollapse.collapse_ctx_following_sequence (Not_found). No backend or source repair. The owned straight-line radix-four reference extracts without external templates. Its generated declarations are split unchanged into 29 dependency-order modules for focused checking. This is P6 preparation, not row discharge. Kani equivalence is running; producer invariant remains required.

Pinned tool fallback: historical charon path missing (exit127); used surviving cb pinned tools read-only. No infrastructure repaired. Lean38000/38001 are failed name inspections;38002 failed elementary numeral opacity;38003 canonical carrier/constructor facts passes (6 standard-axiom reports).
