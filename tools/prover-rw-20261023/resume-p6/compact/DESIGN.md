# ProverRwResumeP6 compact observation after058 timeout

Original058 source and complete failure receipts remain unchanged. It exhausted
240s during symbolic checking, not compilation; there is no counterexample or
new established contract. Do not rerun it or increase any limit.

Isolated shape: original scalar snapshot builds a64-byte array to expose one
byte; the generic array snapshot calls it for each32/64 element, including
pre/post hooks. New source adds a default metadata byte observer to Zeroize;
the scalar impl delegates directly to DefaultIsZeroes' typed u8 observer and
the array collects that Option<u8>. It removes all64-byte scalar snapshots,
element-size checks and element Snapshot construction. Original actual Drop,
Zeroize, volatile writes/fences, caller source, universal errors and assertions
are unchanged. This is an instrumentation shape change, not a restricted input,
forced output or raised timeout/cap. Reverse-patch manifest retains originals.

Use059 as the second and last Kani this step, with identical3G/4G/noSwap/Tasks64,
240s and corrected before/go admission. It supersedes the optional paired check
for this step; that prepared source remains UNEXECUTED and UNVALIDATED. A denied
admission or failed059 stops checks; no additional Kani or extraction. No native
P6/semantic erasure/source adoption inference follows from a failed check.
