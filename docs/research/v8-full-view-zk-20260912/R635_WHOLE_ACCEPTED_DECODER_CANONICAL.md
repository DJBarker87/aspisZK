# R635 whole accepted decoder canonicality

`R635DecoderWholeCanonical.decoder_accepted_canonical` proves that for every
N with N.val ≤ 104, any accepted actual generated `r55_decode_into` execution
returns only U32 values strictly below P=2147483647. The input bytes and
initial output array are arbitrary. It applies to the actual selected C1
104-word and C2 48-word calls. There is no input-canonicality, source-loop
success, chunk-size, write-bound, or final-mask premise: the accepted result
and the small selected-size bound are the only hypotheses.

The proof derives the source header consequences, exact chunk count/size,
complete source execution, final rejection-mask acceptance, and canonicality
across every written block. R632 records the exact replaced array segment;
R634 transports canonicality across that segment; R636 derives positivity,
divisibility by eight, and exact byte length from accepted source execution.
The value P remains rejected. Existing complete decoder error/state
correspondence is reused; negative cases were not weakened or removed.

This proves canonicality, not exact radix-2^31 serialization, full quotient
execution, privacy, or soundness. The next proposition identifies the decoded
values with the actual packed serialization and composes the source quotient.
The universal hiding argument, whole-view simulator, adaptive shared-oracle
losses, coherent pre-beta quotient extraction and optimized acceptance
refinement remain unproved.

## Verification

Pinned Lean 4.32, `lake env lean -j1 -M4500`, one capped systemd scope per
focused job: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128.

| Target | Green run | Exit | Wall | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| R632DecoderBlockArray.lean | 1791108158246819000 | 0 | 2.99s | 3770336 | 0 |
| R634DecoderPrefixCanonical.lean | 1791108335766672000 | 0 | 1.45s | 3749948 | 0 |
| R635DecoderWholeCanonical.lean | 1791108835711646000 | 0 | 2.17s | 3775540 | 0 |
| R636DecoderAcceptedHeader.lean | 1791108643995780000 | 0 | 1.79s | 3768176 | 0 |

All ten requested axiom reports are retained completely. They use only
propext, Classical.choice, Quot.sound, and the previously recorded opaque
`core.fmt.Formatter : Type` for the inherited source unwrap path. The latter
is a type constant, not an assumed behavioral proposition. Successful reports
contain no sorryAx. Failed development attempts, exact sources, checksums,
source revisions and import pins are saved in the evidence bundle. The final
R635 focused check was at revision 93cd6ea38913bf6cd0b8672a6d110c347740ff97;
earlier dependent receipts record their exact earlier revision.

GNU time reports Lean-child peak RSS; wrapper MemoryPeak is not aggregate
Lean RSS. Sources were promoted byte-for-byte from green snapshots. No
unchanged successful check or regression was repeated. The selected Rust
source, security parameters, authentication and negative examples are
unchanged; saved CU remains 999790/999532.

Evidence: [r635-decoder-whole-canonical](evidence/r635-decoder-whole-canonical/).
