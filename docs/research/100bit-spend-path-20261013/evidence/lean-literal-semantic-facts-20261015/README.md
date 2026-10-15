# Literal semantic reader facts

This focused target establishes two list-level facts about the literal semantic-prefix reader. `read_values` shows that successful output field values correspond to the ordinary values carried by the input challenges; `read_semChals` reuses the selected semantic-prefix theorem to show that lifting the decoded message/value pairs yields the expected semantic challenge list.

The target compiled as `R1LiteralSemanticFacts` attempt `a` under Lean 4.32.0, `MemoryHigh=4G`, `MemoryMax=6G`, and `MemorySwapMax=0`; elapsed time was 1.62 s, peak RSS 3,579,296 KiB, and swap 0. Both axiom reports list `[propext, Classical.choice, Quot.sound]`.

These are list-view equalities only. They make no claim about Rust correspondence, accepted proofs, or probability bounds.
