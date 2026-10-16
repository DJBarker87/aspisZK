# Worker A: derived byte/rank and concrete parser provenance

These follow-on results use the checked begin checkpoint at `69da71ea36d4dd511ecfe3204b33c54555d18ca4`. Both targets ran alone, with MemoryHigh=6 GiB, MemoryMax=8 GiB and MemorySwapMax=0. The archive includes successful and failed attempts, exact commands/source/runtime hashes, producing objects, manifests and axioms logs.

| Target | Exit | Wall s | Peak RSS KiB | Swap | Standard-only reports |
|---|---:|---:|---:|---:|---:|
| ExtractedDigest32BeginProvenance | 0 | 2.084 | 3867876 | 0 | 3 |
| ExtractedDigest32PrefixAdapter | 0 | 2.095 | 3868396 | 0 | 5 |

`validated_record_bytes` inverts both actual current accessor bodies: every successful validated record has the requested row and its exact `pre.records[row]` bytes. `begin_row_provenance` derives this byte identity for any of the fifteen actually reached begin rows, along with the exact Digest32 absorb/read1/read2 equations, state carry, existing byte-rank/QM31 sampler equation, and membership in the actual returned challenge fields. Its only execution premise is actual `begin` success. There is no assumed record-byte identity or sampler equation.

`PrefixAdapter.parseAccepted` is a concrete parser, not an arbitrary callback: it calls the accepted extracted `Prefix::parse` and maps only the nominal Prefix and Error carriers. `parse_typedFull` supplies strict `decodeFull`, `encodeFull`, and `decodeFrom` facts for all25 returned records from that concrete parser's success. The current Rust `Prefix`, `Error`, and `Prefix::parse` declarations match their accepted extraction hashes exactly; `source-audit.py --check` verifies this. The current namespace does not contain an emitted `Prefix.parse` constant, so no equality with such a constant is asserted. This adapter is ready to instantiate an explicit actual caller boundary.

The parser adapter uses its accepted prefix cache in a separate workspace. Its102 objects and sources are pinned against accepted manifests/receipts. Eight object-byte conflicts with the sampler cache are inventoried in `prefix/separate-import-conflicts.json`; no combined parser/sampler import compatibility is claimed. The current named preparation Type/Fun pair is identical in both environments.

The exact remaining obligations are:

- Full `hbytes`: construct the actual25-row completed transcript records and prove their message bytes equal the concrete parser's first25 returned frames. The first15 source identities are now derived; actual remaining caller rows are still needed.
- `SelectedCompletedSemantic.semChalsZ_read.hread`: connect that actual completed log to the selected table/challenges. The existing `completed_read_of_decode` can consume the strict-codec result once the full byte/log equality is supplied.
- `htyped`/`ha`: strict-codec typedness is supplied here. The stronger address-context `UnifiedSemanticRecovery.typed`/first-cell premises still require actual Digest32-to-oracle/table correspondence and full source caller/state reachability. They are not consequences of this pure dictionary model alone.
- C2: the literal `Message.c2` carries a `C2Word` with1048576 entries. A32-byte commitment root does not determine that witness. Its source/custody construction and attachment to logical row2 remain separate; no word is invented from the root or a later table.

Run `python3 verify.py` and `python3 source-audit.py --check` for read/hash-only verification. No Lean, runtime harness, or SBF build is launched by these checks.
