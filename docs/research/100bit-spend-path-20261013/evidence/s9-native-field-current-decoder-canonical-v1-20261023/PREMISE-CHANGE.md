# Actual native operand canonicality

Before: full Pair source operand reasoning still needed canonicality/model interpretation for actual weights.field reads, and the S5 reader proof used another nominal reader with checked offsets.

After: the current native transparent byte decoder is proved to map fully to the existing RecordParser, and actual field SUCCESS alone gives decoderSome, all32 source byte-read successes and native canonicality. No desired canonicality/decoder-correctness/data premise is added.

Unchanged: actual source call, bytes/index/output, current wrapping offsets and successful-run event. Changed interface scope is explicit: universal canonicality is proved, but complete S5 checked-reader equality is NOT claimed unconditionally. Large wrapping-index aliases show why a bounded actual caller domain is needed.

No cryptographic assumption is changed. The allocator/Rust/runtime/caller/artifact/fullPair/security obligations are not discharged by local decoder canonicality.
