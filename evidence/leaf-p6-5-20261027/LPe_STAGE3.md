# Checkpoint source cuts and remaining whole-call gap

K014 TIMEOUT90s: actual complete verifier::checkpoint on independent six
canonical wide fields, arbitrary raw scalar fields, all 64 independent weights,
all state/roots/queries/next; S2, proof3/public5 physical byte carriers. Ordered
Digest32 checks all three attempt arguments with independent 32-byte answers.
Even the header projection did not finish. No whole-call property is established.

The timeout is split, never rerun unchanged:
- K015 PASS: copied source header cut, exact16 bytes including usize-to-u8 next.
- K016 PASS: copied proof/public digest and state cut with arbitrary16-byte
  prefix; exactly two attempts [proof], then [public], independent responses,
  retained prefix and all112 output bytes, physical carrier widths3/5.
- K017 PASS: roots and query source loops, independent roots2x32/query22x4,
  checked all152 concatenated bytes. These two nonadjacent source stages are
  concatenated in the harness only; native intervening wide/rho stages remain.
- K018 PASS: ACTUAL private put and put_k functions, arbitrary canonical wide,
  arbitrary raw scalar and32-byte prefix, all80 output bytes/frame.
- K019 PASS: copied semantic-alpha and Z loops, independent14 raw scalars,
  all224 bytes, no diagonal/sparse restriction.
- K020 TIMEOUT90s: copied checksum/append cut on arbitrary1736-byte prefix,
  arbitrary32-byte answer, third-call dictionary (initial count2), checking
  all1768 returned bytes, exact label/payload and count3. No third-call result.

Copied source cuts are identified explicitly. Passing them is NOT a call to
the enclosing checkpoint or a proved extraction/composition of its execution.
Full same-input join, all physical carrier lengths, complete three-digest native
chronology, full64-weight append loop, returned payload++checksum and source/
word/ownership/runtime/artifact refinements stay OPEN. The candidate32-weight
block and other complete-call property projections were NOT launched.

Budget20/20 Kani is exhausted:12PASS/6TIMEOUT/1type-check failure/1unwinding
failure (corrected coordinate comparator passed). No further Kani is permitted.
All20 graph/edge checks and before/after lock hashes passed. No OOM, cap raise,
unchanged timeout retry, scope overlap or swap. See per-attempt receipts.
