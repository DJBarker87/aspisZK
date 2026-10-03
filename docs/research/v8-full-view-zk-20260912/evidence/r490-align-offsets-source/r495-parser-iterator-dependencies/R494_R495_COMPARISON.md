# R494/R495 declaration comparison

Both captures use the same recorded source revision, source hashes, tool hash,
and Rust flags. Comparing the normalized LLBC syntax for existing declarations
(replacing capture-local statement IDs and hash-cons/deduplicated type IDs),
the parser entry `Fun0` (`r105_parse::fields`) and helper `Fun20`
(`slice::align_to_offsets`) have equal signatures and bodies. Their raw JSON
hashes differ only because the additional declarations change those capture
identifiers.

| Function | R494 body | R495 body |
| --- | --- | --- |
| 22 `slice::split_at_unchecked` (first instantiation) | Opaque | Structured, Transparent |
| 23 `slice::split_at_unchecked` (second instantiation) | Opaque | Structured, Transparent |
| 25 `num::unchecked_sub::precondition_check` | Opaque | Structured, Transparent |
| 32 `slice::split_at_unchecked::precondition_check` | Structured | Structured, Transparent |

The direct opaque foreign callees newly visible from those R495 bodies are:

| Caller | Foreign callee | Body |
| --- | --- | --- |
| 22, 23 | 21 `slice::raw::from_raw_parts::precondition_check` | Opaque, Foreign |
| 25, 32 | 33 `panicking::panic_nounwind_fmt` | Opaque, Foreign |

This table records capture structure only. It makes no adequacy, safety, or
source-correspondence claim.
