# Failed steps and replacements

K001/K002: native filled harness failed compilation: exact KMX includes allocator_api. Replaced with scratch-only cfg(kani) feature attribute. No semantic control credit. K003: own unified-diff reader appended the attribute in the wrong location. Replaced with context-checked unified-hunk application; K004 PASS/K005 semantic FAIL.

L001: reserved Lean identifier prefix and nonexistent ReservationError type; L002/L003: list-append proof normalization. Fixed statement/proof, no resource increase. L004 passes. Draft elaboration sorryAx outputs are excluded.

K016: partial local-record window failed unwinding while generating arbitrary2048-byte input; not a timeout, not a mismatch. Bound18 did not cover initialization. Replacement exact bound2050; no stronger input precondition and no timeout/cap change. No credit until replacement and matched control pass.

Stage native byte-window review: K045–K060 cover j<16 only, while S2 callers request n=64. This is a stronger precondition than the caller establishes. No TX2:141 closure from these gates. Replacement must widen scratch and j together to64; same harness names retained, and matched controls rerun for the changed domain. This is a new domain obligation, not an unchanged passing-shape rerun.

K079 init01: CBMC timed out at90s (scope wall95.86688469s, RSS6345004KiB, swaps0), proving combined length/new cell on an unnecessarily independent64-cell prestate. No credit; no rerun unchanged. Replacement restricts the prestate to the ACTUAL filled initialization invariant: an arbitrary prefix p<64 of the SAME arbitrary value. NHM_Filled64.initialization proves that every caller iteration supplies exactly this invariant. No stronger-than-caller condition, no cap/timeout increase, same harness names. Existing broader pointer/move K077/K078 is reused, not rerun. Frame law now concerns the initialized prefix of this owned fresh vector; it never claims arbitrary caller-visible aliases.
