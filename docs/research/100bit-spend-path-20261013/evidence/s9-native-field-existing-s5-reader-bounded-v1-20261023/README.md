# Current native field reader to existing S5 reader

## Established

`native_field_maps_s5_reader` proves full `Result` equality between the CURRENT qualified native `weights.field` and the EXISTING S5 `readerBody actualPairDecoder`, after the structural output map, under `(i.val+1)*32 ≤ Usize.max`. This covers arbitrary bytes, failure/divergence, decoder rejection and unwrap failure. It uses the earlier current-native decoder map, not a renamed new reader model.

`quotient_index_fits` derives a fitting 32-byte window from the SAME successful `Slice.len bytes /32` result and `i<n`. `quotient_index_maps_s5_reader` then removes the separate safe-offset hypothesis. `actual_pair_success_bounded_field_reader` derives the quotient from SAME actual Pair acceptance using the existing checked prefix inversion. It supplies these conclusions for every index below that actual quotient.

## Scope and retained boundaries

The native source uses wrapping offsets. The existing S5 reader uses checked offsets. Their unrestricted equality is false: on a 64-bit architecture, index 2^59 wraps the native 32-byte start to zero while checked multiplication rejects it. The arithmetic witness is retained in the preceding canonicality packet; it was not reported as an executed whole-reader counterexample. This packet proves the sufficient bounded interface, without silently changing either reader.

A particular real dot-loop index must still be connected to this bounded domain. The theorem does not assume or conclude an exact byte length from the quotient. It does not prove whole Pair value refinement, an SDK/runtime wrapper, or a 100-bit security theorem. Source-cut and artifact correspondence remain distinct obligations.

## Reuse and validation

No decoder arithmetic was reproved. Checked offset totality and checked-to-wrapping equality reuse existing R22 lemmas. The generic division theorem supplies the actual quotient value and constant-divisor arithmetic is symbolic. The focused checks ran serially at -M4400 under the shared local mutex. Exact commands, source hashes, revision, exit status, wall time, RSS, swap, axioms and profiles are retained in proof receipts.

The first two reader attempts performed preflight only: missing existing warm adapter, then callback. A read-only 5,142-header closure check selected 223 project objects and 15 companions into one temporary namespace owner. Existing libraries were reused; no cold or complete replay ran. Only selection/hash evidence is stored here; no compiled objects are included.
