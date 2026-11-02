# K-3 static/constant sharing review findings

No historical credit is withdrawn. The provisional NEC_K036 domain finding below is RETRACTED; exact-source replay confirms the original frontier index bound is8. Incomplete migrations remain OPEN.

Own reporting correction: the initial NEK_STAGE2.md incorrectly called K011/012 restored. Both are compile errors (E0593, missed adapter map_err(super::error) after the context-parameter change), with no semantic verdict or credit. The stage note is corrected. K023–030 are eight namespace compile errors. K031 timed out and remains OPEN; K032 is an already-submitted failing control, not restoration.

K052 reached its named harness but the outer 240s scope expired after cold compilation/Cargo-lock waiting. It is OPEN and is not rerun unchanged. The target-only feature selection repairs the compile configuration for other independent windows, without raising any limit.

## RETRACTED provisional NEC frontier observer domain

Source inspection establishes an admitted counterexample in evidence/slice-s-leaves-20261029/NEC_K036/NEC_harness.patch, module NEC_static_decode. GROUP=2; prepare admits INDEX<32 and ROW<20; after_word uses next_frontier[ROW][INDEX], whose inner dimension is8. INDEX=8,ROW=0 therefore reaches an out-of-bounds observer access. after_contract adds no INDEX<8 restriction. The same range is appropriate only to Live pool/domain byte fields, not the After frontier column.

WITHDRAW the NEC_K036 native certificate and any reliance on its universal frontier observation. NEC::decode_pair_afterstate_boxed_v1 remains OPEN; its intended typed boxed-decoder statement is not refuted by this harness-domain error. NEE's six active pure-payment rows are independent of this leaf. No shipped-file bug is alleged. The original counterexample and domain must be retained; a future corrected Fin8 window needs an explicit caller-domain association, not silent narrowing. The local-record replay retains the original INDEX<32 domain and is pending.

Correction: the initial source finding misattributed the generic prepare function from a different receipt to NEC_K036. The exact NEC_K036 module has kani::assume(i<8), not INDEX<32. Therefore INDEX=8 is NOT admitted. NEK_K128 passed and its matched control K129 failed. The provisional withdrawal is fully retracted; original composition credit remains subject to the outstanding local-context/shape/copy checks. This is an own audit error, not a newly demonstrated tool or shipped-code defect. NEK_NEC_FRONTIER_DOMAIN_FINDING.json retains the source hash, exact prepare line and correction. Future per-receipt domain claims must use that receipt's reconstructed source, never a nearby generic variant.

Transitive support correction: NDN_K001 was classified UNAFFECTED from its selected parent file alone. Its receipt-pinned NDN_K001-input-pins.json.xz loads NDE_poseidon.rs (sha256 db4722904121a72fc2c7856e0666af67a7dcdd5786cd7886b98b1182f00f0789), containing written static matrix logs. Suspend that historical receipt pending its exact local-record replay. This is a source-closure correction, not a new semantic counterexample. The exact parent also contains an extra matrix-reply assignment, so NDE_K050's replay is not silently substituted.
