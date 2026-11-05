# Failed steps and replacements

K001/K002: native filled harness failed compilation: exact KMX includes allocator_api. Replaced with scratch-only cfg(kani) feature attribute. No semantic control credit. K003: own unified-diff reader appended the attribute in the wrong location. Replaced with context-checked unified-hunk application; K004 PASS/K005 semantic FAIL.

L001: reserved Lean identifier prefix and nonexistent ReservationError type; L002/L003: list-append proof normalization. Fixed statement/proof, no resource increase. L004 passes. Draft elaboration sorryAx outputs are excluded.

K016: partial local-record window failed unwinding while generating arbitrary2048-byte input; not a timeout, not a mismatch. Bound18 did not cover initialization. Replacement exact bound2050; no stronger input precondition and no timeout/cap change. No credit until replacement and matched control pass.
