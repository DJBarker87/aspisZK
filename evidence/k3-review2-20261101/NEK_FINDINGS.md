# K-3 static/constant sharing review findings

No historical credit withdrawn so far. All incomplete migrations remain OPEN.

Own reporting correction: the initial NEK_STAGE2.md incorrectly called K011/012 restored. Both are compile errors (E0593, missed adapter map_err(super::error) after the context-parameter change), with no semantic verdict or credit. The stage note is corrected. K023–030 are eight namespace compile errors. K031 timed out and remains OPEN; K032 is an already-submitted failing control, not restoration.

K052 reached its named harness but the outer 240s scope expired after cold compilation/Cargo-lock waiting. It is OPEN and is not rerun unchanged. The target-only feature selection repairs the compile configuration for other independent windows, without raising any limit.
