# SourceSamplerByteRank evidence audit

The bundle’s file checksum list, both attempt snapshots and receipts, the final source, direct import source pins, object archive members, and runner hashes were checked independently. All match the bundle manifest. The final source also matches the current worktree source at the recorded hash.

Attempt `a` failed and is retained as a predecessor. Attempt `b` is the green target: exit 0 in 1.67 s, peak RSS 3,807,660 KiB, zero swap, under the recorded 4G/6G/0 cap. The log contains seven `#print axioms` reports, each using only `propext`, `Classical.choice`, and `Quot.sound`; none uses `sorryAx`.

The theorem chain is model-level: fixed 32-byte Aeneas array decoding gives eight words whose positional numeral equals `R0C.ModuloField.blockRank`; arbitrary repeated-pass output agrees with the Nat low-digit model, including the four-pass QM31 digits and eight-pass ordinary digits/quotient; end-around digits have the stated Nat value. It does not prove the extracted Rust sampler loop’s reads, retries, updates, or returned value refine this model.

See `review.json` for hashes, receipts, resource data, and check results. This review does not make a source-refinement or security-closure claim.
