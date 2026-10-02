# R318 published raw prefix evidence audit

Read-only audit; no Lean compile or tracked edit. The outer evidence manifest covers all 19 files with no hash mismatch, missing file, or unlisted file. The published source copy and target both match SHA `e418b302e5b2d9e6808b9cbd467e9c9e371157c6c9bd5817c7e4a75e886b2e14`. The four loop/body definitions byte-match their saved R292 generated declaration blocks and recorded block hashes.

The successful log and manifest agree: exit 0, 1.04 seconds, 2,532,716 KiB peak child RSS, zero swaps, revision `b268da1cb6878d9b1ab6c2cab79b0592d04dd0ca`. The launch script records 5 GiB `MemoryHigh`, 7 GiB `MemoryMax`, zero swap, 128 tasks, and Lean `-j1 -M4500`. All four complete axiom reports match the log and use only `propext`, `Classical.choice`, and `Quot.sound`.

The raw-adapter builder's emitted declaration blocks are exact. The final file differs from its earlier recorded builder output by one wrapper line, `noncomputable section`; removing that line reproduces the old hash `efaf9b8e...`. This is the only staged wrapper delta and leaves all four generated declarations unchanged. Two copied precompile audit fields are stale: the nested `raw-adapter-audit/SHA256SUMS` still records the pre-wrapper target hash, and `binding-audit.json` still says `compiled: false`. The enclosing bundle's SHA256SUMS.json is valid and correctly hashes the final target and copies.

R318 establishes only the elaboration result. It does not establish the forward prefix loop behavior, caller invariants, complete batch, standard-library Rust correspondence, or security. The recorded next step is proof of each forward-prefix step/loop and errors under justified local invariants, followed by deriving caller bounds and reverse initialization from source.
