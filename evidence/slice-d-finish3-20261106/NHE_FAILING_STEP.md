# Failed steps retained

- NHE_L002: CM port elaboration failed on an opaque scalar-size comparison and invalid simp refolding syntax. Corrected at L003; standard-only axioms. No credit from L002's elaborator-generated sorryAx.
- NHE_L006/L007: limb parser carrier proof incomplete, then unsupported tactic syntax. Replaced by explicit map-bind rewrites at L008; standard-only axioms.
- NHE_L009: byte parser carrier proof hit the default 200000-heartbeat limit while repeatedly attempting the terminal limb theorem against every byte-bind prefix. Tool/proof-shape limit, no mismatch. Replaced by terminal-law simplification over the monadic map spine at L010 (2.70s); unchanged heartbeat/caps, no unchanged rerun.
- NHE_L011/L012: field selector proof elaboration errors in numeral projection, rewrite staging and indentation. Correcting the proof; no source or domain strengthening.

Failed elaborations are excluded. No child success premise is introduced to repair a failed step. These are focused Lean attempts, not native correspondence credit or composed closure.
