# Wide parser unrolled extraction candidate (h)

This isolated extraction starts from the original pinned `field.rs` and `field/wide_exact.rs`. The final h2 candidate retains every original `#[inline(always)]` attribute, changes only `WideExact::from_limbs`'s limb-range guard and `WideExact::from_le_bytes`'s parser body, and preserves the destructuring and field-construction code byte-for-byte. The local checker verifies that exact diff.

The final capped Charon/Aeneas attempt h2 succeeded (`--mir built`, no monomorphization; MemoryHigh 4G, MemoryMax 6G, swap 0, TasksMax 128). It completed in 2.25 seconds at 306240 KiB maximum RSS with both extraction and translation returning zero. Translation emitted three nonopaque functions: `WideExact.from_limbs`, `WideExact.from_le_bytes`, and `parse_wide_exact_probe`; it also emitted four types and two globals. The preceding h attempt succeeded but was superseded because its formatting changed nested constructor text beyond the requested byte-exact scope; its complete raw evidence remains preserved.

This is generated Aeneas source only. The generated module has not been Lean-checked or refined against a Rust compiler execution. No runtime source was edited or adopted, and this bundle makes no SBF cost or security claim.

Run `python3 check-candidate-scope.py` to verify source scope and h2 source hashes. The manifest records each attempt, input/tool pins, generated artifact hashes, and the raw h2 result-label typo with a corrected index record. `SHA256SUMS` covers all bundle files except itself.
