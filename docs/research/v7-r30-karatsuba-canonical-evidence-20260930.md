# V7 callback Karatsuba output canonicality

Source parent: `d790f6ba5`; checked source SHA-256:
`099425e3bb37badef3a66ecbb94443d753060261b1c653b140a6a364fa1f95a6`.
Target: `V7ProductionCallbacksR30KaratsubaCanonical.lean`.
Host: `dombarker@100.108.41.90`; pinned Lean 4.32.0, existing compiled cache.
Focused wrapper: `check-r30-decoder-focused.sh d790f6ba5+karatsuba-working
V7ProductionCallbacksR30KaratsubaCanonical` inside
`systemd-run --user --scope -p MemoryHigh=7G -p MemoryMax=8G -p MemorySwapMax=0`.
Scope: `run-rbb3438fe508a4bf49f47a01224fa21f8.scope`.
Result: exit **0**, wall **1.69 s**, peak RSS **2,677,192 KiB**, swaps **0**.

Audited declarations: `successful_callback_reduce_canonical`,
`successful_channel_closure_canonical`, `successful_channel_sums_canonical`,
`successful_prepared_sum_products3_canonical`.
All four `#print axioms` results are exactly
`[propext, Classical.choice, Quot.sound]`.

The three-product helper's successful return is canonical for arbitrary wide
channel values: reconstruction reduces each U64 channel before composing
canonical field operations. This does **not** prove absence of wrapping in the
accumulation or exact dot-product semantics. It is a canonicality-only lemma
for the gamma and normalized-fold chain.

No full manifest or unrelated regression was run. End-to-end V7 closure remains
open pending gamma-combined outputs, normalized fold and terminal composition.
