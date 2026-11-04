# Native substitution register

No field multiplication or Kani function contract is used; LPh field-stub and
ruling-(t) contract-shape rows are not invoked. The frozen source bodies are
unchanged outside cfg(kani) harness hooks in the external scratch tree.

| Substitution | Domain and interpretation | Evidence / status |
|---|---|---|
| Exact KMX ptr::copy_nonoverlapping and [u8]::copy_from_slice | KMX patch byte-for-byte, reached primitive copies; no own stub | Every native receipt pins patch; K019/020 and matched property mutations; KMX_CopyMeaning laws reused |
| Decoder poison in direct frozen rejection harness | Only paths rejecting CPI errors, missing/wrong program/wrong width; decoder must be unreachable | K021/22,34/35,36/37,38/39,59/60; not a positive decoder certificate |
| Local runtime record | Arbitrary return program/bytes or error supplied by runtime law; call log local | K007 continuation; full caller rejection subset; actual Solana runtime remains trust |
| Decoder cut's digest oracle | Arbitrary32 bytes, full seven-variant AtomicStatementError or raw Digest | K054/55,26; CLOSED NEQ child; NFO_DecodeOracle.substitution; error-map law |
| Decoder cut's afterstate oracle | Exact688 input slice, full native result/error | K054,27,31; CLOSED NEX child; substitution/error-map law |
| Decoder cut's validator oracle | All raw result fields, full native result/error | K054,28,32; CLOSED NEQ/NBX child; substitution |

The three local child oracles replace calls in a source-exact cut, not runtime
syscalls or global mutable statics. Joining their pure laws into AcceptedCodec
and transporting the complete caller representation remains OPEN. The canonical
probe/child laws are reused read-only, not copied or renamed for a verdict.
