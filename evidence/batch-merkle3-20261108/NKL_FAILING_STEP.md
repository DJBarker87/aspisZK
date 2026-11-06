# NKL failing steps

E001: Charon exit0; Aeneas internal error InterpBorrows.ml:2731 in loop borrow simplification. No extraction credit. Receipt: wall0.656887945s, peak140976KiB,swap0. Pins/LLBC retained. The shape is retired. E002 changes Children to Copy value passing and unrolls the twelve-position outer leaf loop into outlined leaf_at calls; no tool patch/cap/timeout change.

E002: Charon exit0; Aeneas exit2, same internal site, now localized to the first unrolled leaf_at call (src/lib.rs42). Wall0.640853963s,peak142384KiB,swap0. Both extraction allowances consumed. No emitted-reference proof claimed. Continue under (ay) reviewed transcription; no third extraction.
