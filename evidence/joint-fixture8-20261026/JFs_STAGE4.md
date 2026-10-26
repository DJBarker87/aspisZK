# Complete payment decoder

`JFs_PaymentDecode.source` proves the actual emitted private-transfer decoder
accepts public1880[1664:1880] and returns `JFs_PaymentValue.value`. The theorem
has no decode/header/canonicality/validator-success premise. `common_validated`
and `validated` separately audit both actual native validators at those values.

The exact anchor/checkpoint sequence is42 and asset ID77. Snapshot13/afterstate14
are append indices, not that anchor sequence. Failed037 captured and rejected the
draft's guessed13/0 constants; the source-bound Cell06/07 arrays are authoritative.
No unsatisfiable real-byte requirement or vacuity counterexample was established.
Other rejected drafts and standard-axioms-only final receipts are retained verbatim.

041's reservation scanner saw a vanished foreign cgroup before any Lean process;
the permitted rule7 retry was taken after30seconds, retaining its initial log.
No infrastructure,cap or existing proved source was changed.

Through045:45 Lean process attempts;0 Kani. All local final payment/afterstate/
late proofs use only standard axioms. No top premise removed. Complete public
validation/decoding and serialization are the next stage.
