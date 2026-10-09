# R512 split-precondition source frontier

**Status: source-only FAILED frontier. No Lean proof.**

This bundle preserves the exact selected R500 LLBC and the R509, R510, and
R512 serialization/projection attempts. R512 is the first attempt whose
pinned R497 translator imported the isolated input and reached the retained
source operation. It stopped at the panic-format string raw-pointer operation:

```
&raw const (*msg) with_metadata(copy msg.metadata)
core/src/fmt/mod.rs:815:4-823:5
generated from core/src/str/mod.rs:575:8-575:12
```

That operation is not given a replacement meaning here. The valid branch of
the native source execution remains unproved. No generated Lean was accepted,
compiled, or audited as a theorem.

## Exact source and target boundary

`r500/R500SplitPreconditionSelection.llbc` is the complete selected source
input, SHA-256 `aa06813bc1d0d30cd2f286174e4f2767ecb9625b6aee3aa6f678d723b6f107fd`.
It preserves the full declaration table while its five selected rows are
Fun32, foreign Fun33, and Types15/16/17. The recorded original function edge
is Fun32 -> Fun33. This bundle does not add panic semantics or any other
source edge.

R512's rewrapped input has SHA-256
`b919ee8060efbbfccd749731f7930df44bf86d5b24c23d5141c1f9b9269e4e8e`.
Its audit retains exactly function rows Fun1, Fun32, and Fun33, inserts ordered
Fun1 immediately before Fun32 for the metadata prepass, and records that its
independent decoded projection equals the fully expanded original projection.
All types, globals, and traits are preserved under that decoded comparison.

## Attempts

| attempt | result | exact first boundary |
| --- | --- | --- |
| R500 | exit 2, 0:00.16, 57,024 KiB RSS, swap 0 | global PrePasses visited unselected Fun8 `chunks_exact::<u32>` and rejected its U32 slice against concrete U8 `slice_len_fn` |
| R509 | exit 1, 0:00.09, 50,336 KiB RSS, swap 0 | nulling rows removed a hash-cons definition needed by retained Fun1 |
| R510 | exit 1, 0:00.10, 51,568 KiB RSS, swap 0 | fully expanded JSON is not accepted by the pinned hash-cons input decoder |
| R512 | exit 2, 0:00.18, 57,728 KiB RSS, swap 0 | imported then stopped at the retained panic-format string raw pointer above |

Each subdirectory includes the copied launch record, complete raw translator
log, receipt, exact input, and applicable serialization audit. The launch
records pin the R497 binary SHA-256
`85a1037c1d2e675907c4a9c3b0b87e671633f9284775b1be8720f8f208b4086b`,
source revision, cgroup caps (MemoryHigh 5G, MemoryMax 7G,
MemorySwapMax 0, TasksMax 128), and input checksum.

## Arithmetic context only

The published [R499 chunks-constructor arithmetic](../r499-chunks-constructor-arithmetic/README.md)
proves quotient/remainder partition and index bounds for positive chunk sizes
4 and 16. It is caller arithmetic only. It does not prove `ChunksExact`,
`split_at_unchecked`, raw pointers, native allocation, iterator behavior, or
the valid source branch reached by this frontier.

## Prior capture reference

R495 is intentionally not duplicated here. Its exact parser/iterator source
capture is the prior artifact at
`.r21-scratch/r495-parser-iterator-dependencies/R495ParserIteratorDependencies.llbc`,
SHA-256 `28ae0b878a54842a705ed71f4ab4fe374edc8b6530170d729bbce79945e1e24b`.
R500's `SELECTION_MANIFEST.md` and copied dependency inventory identify the
source projection from that capture.
