# Actual Pair quotient64 and bounded partial-dot index

`shift_two_val` proves the source wrapping right shift by2 equals division by4 for arbitrary Usize. It uses the platform lower bit bound, BitVec shift-to-Nat law and symbolic arithmetic; no concrete machine modulus is evaluated.

`expected_length_twofold` proves forward execution of the actual source pair_loop0: exactly two source Range.next steps shift1024 to256 to64, followed by iterator exhaustion. `actual_pair_success_quotient64` composes that execution with the existing SAME accepted Pair prefix and its actual length guard. It derives the actual successful Slice.len f/32 result64; it does not infer f has exactly2048 bytes.

`index_exact` proves the native partial-dot wrapping index16*s+j is equal to its natural arithmetic value and below64 when s<4 and j<16. `index_maps_s5_reader` composes it with the earlier quotient-domain bridge, yielding full Result equality to the EXISTING concrete S5 reader at that same index.

The actual source shared/partial loop membership and complete product meanings are separate pending consumers. These theorems do not prove whole Pair semantics or 100-bit security. Only the expected-length loop itself has a forward totality claim here.

Both focused checks passed with standard axioms and zero swap. The first quotient source attempt failed on a BitVec rewrite frontend mismatch and an unreduced known tuple in the terminal step. Version3 uses a direct existing shift theorem application and terminal tuple beta reduction. Version2 was not compiled. No memory or resource settings were raised, and no full replay ran. Exact sources, receipts, failures and dependency pins are retained; no binaries are included.
