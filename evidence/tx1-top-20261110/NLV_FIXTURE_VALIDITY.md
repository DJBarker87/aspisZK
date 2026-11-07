# Native fixture validity and retired shapes

No fixture or passing local window is a native row root. Full physical Cut
production and every caller domain remain OPEN.

K002 full-fixture construction (unused Prepared/accumulator/geometry/pending/
checkpoint at an early parser error) is RETIRED. K007's coupled prepare-prefix
window (error/order + public tuple + scratch + full canonical arithmetic
havoc) is RETIRED. Neither gets a control/replay/credit at its old shape.

Replacement: separate each first-error, public-forwarding, and scratch-entry
window, with the SAME source prefix and independent Error reply; use bounded
u16 observation indices whose exact 0..57606 domain covers the whole 57607-byte
proof, and compose cell facts in Lean. No Rust input is narrowed by this index
encoding. Full declared scratch footprint is still havoced.

The proposed arithmetic-free WideExact input sampler transmutates eight
arbitrary u32 words, each constrained <2147483647, into E. This is an INPUT
fixture/oracle payload, not a replacement for any frozen field operation.
The frozen field sources define E as two QM31, each two CM31, each two M31(u32),
with no enum/reference/invalid-bit carrier. Native size/align assertions check
E=32 bytes/align4 and QM31=16 bytes. All eight words are independent and
canonical, so field-order permutation does not restrict the represented
canonical E values. The sampler never asserts a digits-to-coordinate mapping
and never infers a payload from an address. Actual E values are canonical by
the closed field/Prepared producer domains; their SAME-call installation still
requires the parent proof. No multiplication law is proved in Kani.

These validity facts and native cut-source association must be reviewed by the
next ledger gate. This note does not supply physical ABI admission or new trust.
