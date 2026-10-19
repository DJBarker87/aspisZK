# R17 reverse-bit and table-power proof packet

This packet freezes source and focused evidence for the new V5 reverse-bit owner, its minimal natural-number copy, the copy/source bridge, the table exponent split, and the bounded Nat-residue to ZMod power recurrence. It is source/evidence only: compiled `.olean` files are deliberately excluded. Each accepted receipt records the object hash and exact owner/import hashes.

All Lean checks used Lean 4.32.0 (`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`) in focused NUC scopes with `MemoryHigh=1GiB`, `MemoryMax=2GiB`, `MemorySwapMax=0`, and the shared fresh-admission runner. The receipts, preflights, commands, Lean logs, and GNU-time logs are under `evidence/`.

## Accepted targets

| Target | Source SHA-256 | Object SHA-256 | Attempt evidence |
| --- | --- | --- | --- |
| `AspisFormal.V5FriBitReverse` (fresh owner; unchanged maintained source) | `f694182b0b5d2ea4cb2c33bb81528ec05690ecc01a43cdfc6c9e978cbf5b7542` | `1e5137a1c92e31dff48fd50924f524c0024d7e9ff37ee942cbc7043502ba5f72` | `evidence/v5-owner/` |
| `R17MinimalReverseBits` | `8f4395e2b626ccf9460ada2e77983465ef43eaa180567d29d3f7e45314e6ac6f` | `84cc9dde9a751664f5b18f0ac57080f77df9448930a36c9219c0e3c6347cf33e` | `evidence/minimal-reversebits/` |
| `R17MinimalReverseBitsBridge` | `6fdb92a571c3daadc4724b51fa6066c8147bca2d43161eda600acb17f96b3af3` | `0b9f69bb65cef501bae02d2d62971b7ef90d593ae3c0c49dc1ec953a01ee6f77` | `evidence/reversebits-bridge/` |
| `R17TableExponentDomainBridge` | `c7327b7b7afdf0c4e6d0970e7e201cc841c27f6f764119cb9e86c3217ac31c28` | `90778fb98a2083bcde6f1281e51a297fd7d114e8f889876544ced9851e434f22` | `evidence/table-exponent/` |
| `R17TableBasePowerProbe` | `72e46fd2fce82b9b4c26480ae9f6187d100deabb78f9a25d471c26eece28ff49` | `606f64ec46dd8afede958fe5d69947c94929a1f905a09c7e1821c6e0ee5553ff` | `evidence/residue-probe/` |
| `R17TableBasePowerBridge` | `0f217cdf6f7e361a204ed3ac78f82367af3c3aa1f2ea297a3a6020b66c9b9cb9` | `baa6d8a0b114fc766edd567bad4c6707acab38f833ddd8168c8481d88579ce3d` | `evidence/residue-zmod/` |

The fresh V5 source hash matches the maintained file byte-for-byte. The fresh isolated owner compilation repaired an import/cache problem: repeated prior imports through an older cached owner hit memory failures. This packet does not claim the prior source differed; the environment/object was isolated and rebuilt from the unchanged pinned source. The new owner has no `sorryAx` in its audited reverse-bit theorems.

The residue bridge proves the custom bounded Nat pair operations and their binary power recurrence commute with `ZMod P` pair operations. It does not yet identify that pair multiplication with the maintained circle-group operation or prove that every stored table literal is a ZMod/group-power value.

## Representative A00 chunk

`R17TableAChunk00Certificate.lean` proves all 32 ordered literal pairs from `TABLE_A_chunk_00` by a shared binary half-power chain (597 intermediate power facts), rather than recursively expanding duplicate power expressions. Its input adapter is pinned to source `Funs-chunked-adapter.lean` SHA `f1c1765883a09cc9d9ec926127efbd3810f9f60cf5c77893d35b633e5288bb3f`; `sources/check-A00-adapter-v2.py` verifies all ordered pair literals against that source. The target also proves the first literal’s transport to the generic `ZMod` power model. This is a representative chunk, not a proof of the remaining table chunks or the circle-group identification.

A00 source SHA `f0be97cfe0f55e2d45d2f1ef58364f70ce14af3bc55882afb097f1ca9d5179f0`; object SHA `96ed6932581517707e17434fc6defb7f2da6958db8a07b5a20c565abeff6b259`; receipt/preflight/log at `evidence/A00-chunk00/`. Exit 0, 15.845 s, process RSS 2,268,788 KiB, cgroup peak 616,534,016 B, swap 0. Printed axioms for `entry_00` and `entry_00_zPow` are `[propext, Classical.choice, Quot.sound]`.

Failed earlier A00 proof shapes are preserved in their immutable NUC attempt directories: direct recursive unfolding hit max recursion depth; the subsequent one-step bridge drafts had parser/recurrence-equation errors. The accepted v7 changes the proof shape by sharing powers at each halving step.

The normalized focused-extractor-proof-packet-v1 manifest includes the separately retrieved existing minimal reverse-bit receipt and exact audit source. No Lean check was repeated to assemble it. All 32 A00 equalities are compiled; only entry_00 and its ZMod bridge have printed axiom reports in this chunk. This is not a final full-table release replay.
