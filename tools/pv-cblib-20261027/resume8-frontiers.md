# Native and extraction frontier review

Routes: op26 P6; op30 P6; op31 P6; op33 P6; op36 P6.
No native production source or build changed. No row counterexample found.

- op26: the byte reference matches Unix Path::join on arbitrary byte strings
  of length 0–2 in each operand, arbitrary output coordinate (resume8-join-two-r01).
  Complete safe reference extraction still stops at loan/destructor validation.
- op30: safe empty-byte reference extracted with no external template, and
  checked empty-only String decoder. P6 n≤4 contents/capacity link passes.
  Capacity and recoverable allocation effects are not equated with String bytes.
- op31: borrowed Vec byte append extracts to the standard Aeneas
  `Vec.extend_from_slice CloneU8` primitive, no external template. Native valid
  UTF-8 lengths 2+1 passes against that exact byte operation. Generic String
  representation transport now passes (41671/41681), and the seven-law
  publication passes (41683). Native/unbounded/deployed limits remain.
- op33: borrowed update avoids structured Drop and extracts, but its
  `Vec.remove` leaf is foreign and absent from the Aeneas library. 41588 rejected;
  no invented remove definition, external template, or row credit. A two-u32
  length-0–2 native gate times out at180s; no multiplication is involved and no
  unchanged retry is scheduled. Existing concrete Result<Word,Error> frontiers
  remain relevant; the scalar gate would not alone close their association.
- op36: two-u32 success gate fails a memcmp unwind assertion (bound4,8 byte
  comparison), not the ROW. It is rejected evidence. The final length0–2,
  N=3 rejection gate uses unwind12 before its first execution and passes,
  retaining the error Vec. No success certificate for N=1024 is inferred.
- op32: exact allocator-effect deferral is retained verbatim in NATIVE-EFFECTS.md.

All six Kani runs are spent: capacity, append, pop, array success, join, array
rejection. No chained field-arithmetic check ran. The timed-out pop scope was
observed inactive (run-r65512e83a2df4d0f9f3ae61bfd74cff5.scope); wrapper RSS is
not represented as aggregate solver RSS. Host solver temporary-file ownership
must be established before any cleanup; no shared /tmp sweep is permitted.
