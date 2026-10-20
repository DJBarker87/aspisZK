# S3 pair low-array projection

This source-only packet proves that the explicit-ops `weights.s2_twofold_low_array_model` succeeds from canonical low inputs, and its ordered 16 outputs map to the existing low-step model outputs. The proof lifts the model's successful P6 `from_fn` trace transition by transition using the checked actual callback Result equality and quarter-squared field result; it does not assume per-cell callback successes. It also returns exact closure preservation and final cursor value 16.

The Rust standard-library correspondence for `core::array::from_fn` remains P6, supported by the separately pinned differential test. This packet does not close the enclosing optimized `Weights::pair` caller or production source/adoption.

Run the source-only integrity check with `python3 check_packet.py`. OLean files are deliberately not included; object paths and hashes are recorded in the receipt.

Integration note: source and object pins plus the recorded local axiom audit establish the checked model result. Exact Git HEAD at launch was not captured; the receipt honestly retains a post-compile observation. The historical command also includes Elab.async=false. This packet is retained as an inherited checked model component, not as a final release-complete verification receipt. No unchanged replay was run to conceal or cosmetically repair these gaps. Direct owner paths below resolve to tracked producer source snapshots.
