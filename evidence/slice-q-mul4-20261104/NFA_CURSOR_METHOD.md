# Specialized StepBy native state candidate

Full local record with Range.start, specialized Range.end remaining counter, step_minus_one and Bool first_take. Constructor calibration exercises every start≤26. Arbitrary-prestate step covers each batch0..7 and both Bool values, proving all fields, next reply and size_hint. No field multiplication, static log or function pointer. Native host/compiler representation only, not a portable Rust ABI or SBF result.

Use this packet only after both calibration and arbitrary-prestate pairs pass and exact-source KMX controls pass. The Lean association must relate native cursor4*n (including terminal28) to model min(4*n,26), with remaining7-n. Never identify their raw Range.end fields. Source review: predecessor NEV_RUST_STEP_BY.rs.txt at pinned revision53732d5e0; compiler/backend pins are per receipt.
