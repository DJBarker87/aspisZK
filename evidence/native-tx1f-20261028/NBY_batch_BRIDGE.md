# NBY batch bridge

OPEN. Target is same proof/Prepared/scratch/log across sorted keys, leaf
requests, duplicate/new/error continuations, count, padding and verifier,
then all three trees. No independently successful calls, final accepted scan,
final count, scratch identity or final log is assumed as a bridge premise.

NBV/NBJ/NBI/NBE results are imported. Runtime digest values retain the named
U00/runtime boundary. No multiplication is run in Kani. Fields or runtime
results are not fabricated to prove acceptance. This report will distinguish
local passing cuts from the unestablished parent association.

K041/042 PASS / expected FAIL: actual C1 batch_leaf and the new-entry write
on one arbitrary832-byte window and full idx/val carrier, including salt byte,
payload pointer/length, exact reply byte, d/key_position advance and local
one-call clock. K043 outside-frame, K045 C2 inside and K049 folded inside TIME
OUT at90s. Matching controls are deferred, as are the same outside-copy shape
for the other trees. No timeout is turned into credit or retried unchanged.
Full leaf traversal remains OPEN (global opening and duplicate/error/frame/log
association). The internal clock domain is retained, per NBY_DOMAIN_FINDINGS.md.

K053–K064: all six padding gates PASS with matched failing controls. They
exercise actual slot(proof,s) from arbitrary57607-byte proof; capacity guard
before slicing; first chunks_exact step, arbitrary cursor and full5504-byte
backing; fixed-eight-byte predicate with Parse/Merkle/Ok continuation; exact
empty tail; and local read-only byte frame. Existing NBJ_PaddingPort.physical_scan,
NBJ_Padding.word_exact/scan_exact, NBJ_PaddingBits.zero_iff and NBI_Padding's
first-stop induction are reused. The actual count/same physical scan association
and its continuation into the live verifier remain OPEN, not assumptions.

NBY_RowCopy.windows_eq/row_cells (L005) composes one-byte KMX windows on the
same evolving memory into the exact full row image and every outside byte.
Exit0,4.017990966s,4433868KiB,swap0; standard axioms only. This discharges a
value/frame composition obligation; native source/callee association is separate.
