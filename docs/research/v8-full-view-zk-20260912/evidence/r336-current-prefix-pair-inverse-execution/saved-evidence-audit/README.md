# R335/R336 saved-evidence audit

Read-only independent audit; no Lean run or tracked-file modification.

Both promoted bundles pass their checksum manifests, target/source-copy identity, expected SHA, full axiom-report comparison, resource caps, and successful log metrics. Compile revision is `d04d10ffd971f0821e29afcbb6d04528a2873f9c`; current checkout later advanced to `37d5dd7ecb2c6f7b98822147522b043884ef77d9` for R333 evidence, and the compile revision is its ancestor. R335: exit 0, 0.97 s, 2,526,928 KiB RSS, 0 swaps, two reports. R336: exit 0, 1.68 s, 3,710,716 KiB RSS, 0 swaps, five reports. All seven reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

R335’s two fragments match the pinned R292 input byte-for-byte at lines 543–558 and 559–568; the recorded input SHA is `4d40a5b7…d95aec4`, and operation replacement count is zero. The successful binding probe resolves the retained operation names to selected B.mul, B.inv, and Slice.last declarations. It is a binding check, not independent Rust/compiler/standard-library correspondence.

R336 proves the second-prefix function equal to the first by `rfl`, handles empty slices as `arrayOutOfBounds`, and proves the prefix result under explicit nonempty and canonical encoded-read conditions. The pair inverse theorem preserves its complete result: zero product gives `assertionFailure`; otherwise it returns the encoded inverse seeds. It adds no nonzero or capacity premise; no successful inverse is assumed. Full guards, reverse/output setup, source library/compiler correspondence, and whole callback/privacy/security remain open. Both rejected drafts and their failed logs are retained; `sorryAx` appears only in those rejected outputs.

The initial revision checker expected old compile revision to equal current HEAD. That rejected check and its correction are recorded in `revision-check-initial.json`; the final check verifies ancestry without rewriting the recorded compile revision. Machine-readable audit: `audit.json`; reproducible checks: `check.py`.
