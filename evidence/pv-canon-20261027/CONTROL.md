# Six Kani control checks

These harnesses model only indexing/control expressions inspected in the shipped
source. They contain no field arithmetic and no stubs. They are not a
shipped/reference gate. Time is expected in tiny optimized compilation and
small bitvector control assertions, never finite-field elimination.

1. op121 radix-four indices: block<7 => 4*block+3<28.
2. exact seven-block descending schedule, no duplicate block.
3. interpolation sample index cast <P.
4. interpolation basis reverse-cell and predecessor bounds.
5. ten semantic round tags in 15..24.
6. sampler byte-word and digit indices.

Lean separately proves the mathematical indexing facts; the Rust harnesses
are supplemental control-model checks. The op121 source law stays P.
