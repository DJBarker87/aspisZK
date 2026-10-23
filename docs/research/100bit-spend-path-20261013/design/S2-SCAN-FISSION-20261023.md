# Native source scan probe erasure

S2, S1 and S6 remain OPEN. The 100-bit target is not established. No frozen
production source, protocol, SDK or artifact changed.

The explicit scan-fission noninterference gate retained by
`S2-FORWARD-CALLER-20261023.md` is checked within the constructor-ready native
SDK input class. Both probe bodies and the entire instrumented stage1 body
are unchanged from that packet. Collapsing the single let/any/probe block
restores the ENTIRE frozen production stage1 body byte for byte.

At the actual original-SDK scan site, an enforced empty write contract for
scan_enter passes all2955 enabled non-cover properties, including assertions,
safety and unwinding checks. Both covers are reached. A separate contract for
the unchanged scan_leave checks all Boolean hits and old Option values: only
the designated ghost field may change, and its value is Some(the SAME hit).
All110 non-cover checks and both covers pass. No SDK/guard/Drop replacement or
verified callee stub is used. Existing pure scanner/comparison and typed child
cuts retain their original interpretation obligations.

`S2SdkScanFissionV1` proves complete Result-level ghost erasure, exact reporting,
and zero original model bytes from the same false report. Invalid-slot failure
and divergence are preserved by erasure; the zero consequence requires the
explicit source cell read. The existing total scanner/iterator proofs are
reused. The already checked concrete native iterator constructor/one-step join
is reused, rather than repeated. This does not establish an arbitrary SDK heap
representation or a single joined native caller execution.

| Target | Exit | Wall s | Peak RSS | Swap |
|---|---:|---:|---:|---:|
|sdk-shared-prefix-codegen-scan-fission-enter-v1|0|1.671|541592 KiB|0|
|sdk-native-scan-fission-enter-v1|10*|77.939|3922476 KiB|0|
|sdk-scan-fission-leave-check-v1|0|0.803|199968 KiB|0|
|S2SdkScanFissionV1 / s2-sdk-scan-fission-v1|0|14.876811167|2245378048 bytes|0|

*Raw CBMC exit10 consists solely of the two reached cover properties (SAT).
Every enabled non-cover property is individually reconciled with the exact
property inventory and is SUCCESS. No properties were omitted to obtain this.

NUC jobs received fresh admission, optimized Rust, one job, MemoryHigh6G,
MemoryMax8G, MemorySwapMax0. Local Lean used the atomic lock, -j1 -M4400;
all four axiom reports contain only propext/Classical.choice/Quot.sound.
No unchanged full replay. Parent source revision6cec9df76e; exact per-target
source/tool/command/resource receipts and metadata are in
`evidence/s126-current-caller-20261021/sdk-scan-fission`, with source-only
manifest. Its local path dependencies are checked against the unchanged
constructor dependency sources. Exact Lean import/object hashes are recorded
in `scan-fission-import-pins.json`; no compiled objects are distributed.
The source freeze and transitive adoption/re-pin qualifications remain those
of the forward-caller document.

Audit commands (no prover replay):

```
python3 tools/s126-sdk-modular-20261021/check-scan-fission-packet.py
python3 tools/s126-sdk-modular-20261021/check-sdk-iterator-packet.py
```

Remaining enclosing premises are unchanged except for this local gate:
instantiate original-input metadata/guard facts and the FOUR child observations
(decoded, validated, encoded, firstReturned) from the SAME native execution;
fixed external inputs, original native output frame via copy/implicit cleanup,
actual child/syscall/oracle interpretation, general runtime/ABI and cross-TX
save/resume binding. The native iterator join and extracted any induction do
not alone supply this common-execution certificate. The native accepted-class
coverage and whole R22 totality obligations remain. No source adoption decision
is needed for this instrumentation-only evidence.
