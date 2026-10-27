# Reached claims decoder splits

Exact native library target: ValidatedRecord{row:25,framed:&b}.decode_k::<29>
on arbitrary3717-byte b (5+116*32), offsets0/29/58. Header and every payload
byte are arbitrary. The reference uses real QM31::from_le_bytes on each low
16-byte half, retains the first NonCanonical row/value error, and compares
all29 returned values. No child or allocator is stubbed. This does not claim
Prefix validity, a validation-token producer, allocation success or the unsafe
three-row Box writes in claims.

K006 offset0 TIMEOUT; K007 offset29 PASS; K008 offset58 TIMEOUT. The two failed
offsets are split by canonicality of their first15 values (K009..K012): both
EARLY-error classes PASS; both first15-canonical/LATE classes TIMEOUT. The
classes are exhaustive, but only the early halves are closed. Exact remaining
decode stages: offsets0 and58 with canonical first15 values, then the last14
values and full output/error comparison. Further split those classes; do not
retry any failed shape unchanged. The complete claims storage/ownership and
source/model/native carrier join is still open.

Native domains are inhabited: all-zero payload for the canonical-prefix
class; a P limb in the first value for the early-error class. These are local
witnesses, not joint non-vacuity of the deployed theorem. No new trust item,
axiom or security assumption. Actual-top premise delta T0/P0/G0/C0, removed/
added/changed0/0/0. Full identical before/after statements are retained.

Twelve Kani runs used so far (3PASS,8TIMEOUT,1compile failure). No cap or timeout
increase. Per-attempt receipts retain command, source/dependency pins,
revision, exit, wall, RSS, cgroup peak and swap0. Kani axioms audit is N/A.
Next: focused generic Lean proof and missing immutable model objects, then
four echeck tail classes, two expansion read/write classes and frame/producer
checks. Full scanner/validator and expansion outside-frame harnesses are in
the patch but remain UNRUN under the20-run allocation.
