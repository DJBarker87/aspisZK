# PoolM stage 0: source freeze and changed method

Source revision: 2d30c4c7e41624600de83442cbbe6a7038286aa0.
Only PoolM_ modules and this owned evidence directory may change. No shipped
source, keys, features, artifacts or other workers' files are changed.

Target remains exhaustive dispatch noninterference, including errors and prior
effects. Budget: 100 Lean attempts, 20 leaf Kani runs. Used: 0/100, 0/20.
No all-handler closure is claimed. AS8D and ASPP source-order correction is
retained; their pre-guard arithmetic/CPI effects must not be erased.

First extraction isolates the literal ASPX prefix through both plan metadata
checks, before data borrows, hash, close, refund, resize or assign. The signature
omits unused runtime/hash/return-data parameters and returns unit at the cut.
PoolM_SLICES.json records exact production source byte spans and hashes. The
parser and unique-account loop are included, not assumed successful. The native
SDK data_len and pubkey/syscall leaves remain explicit extraction boundaries.
No whole-prefix Kani is proposed. Existing pinned Charon/Aeneas and S2W runners
will be reused unchanged in the coherent SInt2 workspace.

All mandatory handoffs and security/proof rules have been inspected. Relative
S2 handoff paths resolve under docs/research/100bit-spend-path-20261013.
No release result or new theorem yet: attempt/axioms/RSS/swap fields N/A.
