# Native call-window principle (domain evidence only)

Each scratch hook precedes an actual frozen call and observes exactly its
argument expression. The cfg(kani) block then returns a dummy error, so no
suffix is executed. NED_WINDOW_ERASURE.json verifies exact release erasure.
No `assume(false)`, function pointer, Option<fn>, custom copy stub, field
multiplication, SHA implementation, or whole-buffer native comparison is used.
The original KMX patch is applied exactly; every credited window has a matched
inverted assertion failure under the same source/graph/features/KMX pinset.
Positive cover properties establish reachability of both statement variants.

The caller's earlier opaque replies are abstracted only to check domains.
An arbitrary success/error tag represents whether control reaches this site;
all errors immediately return. Payment bytes are discarded before the later
validator sites; before the encoder payment site only the root reference is
observed, independently of earlier local output writes. Earlier digest replies
are arbitrary bytes and KMX frame/disjointness laws show prefix writes cannot
reach the late window. The late reply abstractor does not establish its output
value. Root input records have ordinary shared references and no interior
mutability; mutable output is a distinct local array. Native physical carrier,
source-to-ELF and callee value/effect association remain explicit obligations.

These are universal argument/domain facts about reachable call prefixes,
NOT proof_for_contract or stub_verified credit and NOT a full root bridge.
Overapproximated stubs are never promoted as functional callee proofs. Their
remaining exact Result/state/effects laws must come from CLOSED callee bridges
and a same-execution composition certificate before NDT promotion.

| Class | Actual expression/domain | Native evidence | Lean value lift |
|---|---|---|---|
| shared parent reference | encoder validator receives the same `statement` | windows 0 | NED_EncoderCallDomains.validation_same |
| shared field reference | encoder digest receives historical anchor | window 1 | NED_EncoderCallDomains.digest_same |
| disjoint mutable subwindow | encoder late receives transition, output[144..1664], length 1520, one arbitrary zero byte, base+144 | window 2 | NED_WindowExtensionality.late_zero, prefixes_frame; NED_EncoderCallDomains.late_domain |
| variant field reference | encoder/validator payment receives the selected variant's original public reference | windows 3, 6 | NED_EncoderCallDomains.payment_same; NED_ValidatorCallDomains.payment_same |
| copied value | validator output-lane receives a copied tuple nullifier, checked at arbitrary limb <8 | window 4 | NED_WindowExtensionality.array_ext; NED_ValidatorTrace.lane_same |
| local initialized window | validator late receives transition and a fresh length-1520 zero window, arbitrary byte checked | window 5 | NED_WindowExtensionality.late_zero; NED_ValidatorCallDomains.late_domain |

The copied-nullifier case deliberately uses value equality. Its local address
is not the address of the root record's field. No native observation is
silently identified with a model record or with an account-data allocation.

Composition trust option A is retained as P6/D188 semantic-transport trust,
reported as reclassification, never removal. No NDT composed row is CLOSED by
this domain-only packet. The model's total codec laws discharge model-level
inner hypotheses only; a missing native leaf remains OPEN.
