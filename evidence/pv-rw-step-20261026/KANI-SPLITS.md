# Kani split table

Every row has its own preflight, full output, resource receipt and exact Rust input snapshots. All use no stubs,6G/8G/swap0/Tasks64 and a240-second timeout.

| Harness | Bound | Result | Wall seconds | Receipt |
| --- | ---: | --- | ---: | --- |
| `compression_state_step` | 2 | timeout; no certificate | 240.01 | [pv-rw-step-compression-001](pv-rw-step-compression-001/receipt.json) |
| `compression_accumulator_c0a` | 2 | timeout; no certificate | 240.00 | [pv-rw-step-accumulator-c0a-002](pv-rw-step-accumulator-c0a-002/receipt.json) |
| `primitive_split::scale_c0a` | 2 | timeout; no certificate | 240.00 | [pv-rw-step-scale-c0a-003](pv-rw-step-scale-c0a-003/receipt.json) |
| `primitive_split::add_c0a` | 2 | PASS | 0.37 | [pv-rw-step-add-c0a-004](pv-rw-step-add-c0a-004/receipt.json) |
| `compression_iterator16_next` | 18 | PASS | 11.79 | [pv-rw-step-iterator16-005](pv-rw-step-iterator16-005/receipt.json) |
| `scalar_mul_wrapper` | 2 | timeout; no certificate | 240.00 | [pv-rw-step-scalar-mul-006](pv-rw-step-scalar-mul-006/receipt.json) |
| `compression_m31_suffix_next` | 18 | PASS | 2.78 | [pv-rw-step-m31-next-007](pv-rw-step-m31-next-007/receipt.json) |
| `compression_initial_state` | 2 | PASS | 0.30 | [pv-rw-step-initial-008](pv-rw-step-initial-008/receipt.json) |
| `reduce64_wrapper` | 2 | PASS | 0.31 | [pv-rw-step-reduce64-009](pv-rw-step-reduce64-009/receipt.json) |
| `sampler_single_limb` | 2 | PASS | 28.57 | [pv-rw-step-sampler-limb-010](pv-rw-step-sampler-limb-010/receipt.json) |
| `sampler_reverse_iterator_next` | 10 | PASS | 0.60 | [pv-rw-step-sampler-reverse-011](pv-rw-step-sampler-reverse-011/receipt.json) |
| `scalar_product_casts` | 2 | PASS | 13.55 | [pv-rw-step-product-012](pv-rw-step-product-012/receipt.json) |
| `scalar_mul_literal_body` | 2 | timeout; no certificate | 240.00 | [pv-rw-step-scalar-literal-013](pv-rw-step-scalar-literal-013/receipt.json) |
| `compression_step_matched_borrow` | 2 | timeout; no certificate | 240.00 | [pv-rw-step-matched-014](pv-rw-step-matched-014/receipt.json) |
| `compression_matched_accumulator_c0a` | 2 | timeout; no certificate | 240.00 | [pv-rw-step-matched-accumulator-015](pv-rw-step-matched-accumulator-015/receipt.json) |
| `sampler_array_state_step` | 10 | PASS | 52.11 | [pv-rw-step-sampler-array-016](pv-rw-step-sampler-array-016/receipt.json) |
| `compression_matched_power_c0a` | 2 | timeout; no certificate | 240.00 | [pv-rw-step-matched-power-017](pv-rw-step-matched-power-017/receipt.json) |
| `sampler_load_word_step` | 34 | PASS | 1.27 | [pv-rw-step-parser-cell-018](pv-rw-step-parser-cell-018/receipt.json) |
| `sampler_load_words_all` | 34 | PASS | 1.40 | [pv-rw-step-parser-all-019](pv-rw-step-parser-all-019/receipt.json) |
| `sampler_decode_words` | 34 | PASS | 0.51 | [pv-rw-step-decoder-020](pv-rw-step-decoder-020/receipt.json) |
