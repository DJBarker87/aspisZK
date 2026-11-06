# Failing attempts

NKG_K010: own source fission introduced overlapping mutable borrows by nesting both log calls. Compiler failure, no native credit. Replacement K013 stores the first reply in a local, preserving original Rust evaluation order. K013 passed; K011/K012 semantic controls failed. No shared infrastructure changed.

NKG_K020: unexpected positive failure, 1/822 checks at core panicking assert_failed_inner, 34.082582716s wall, 1766960KiB peak RSS, zero swaps. Prepared-stage structured Eq assertion has no credit. Replacement K032 keeps the SAME harness name and checks an arbitrary raw cache word (nine-word complete-record extensional assertion), with controls K033/K034. The verdict is not renamed or reclassified. Diagnosis remains pending; no shipped-code bug claimed.

Lean L003/L005/L006/L009/L013 were local elaboration failures (numeral coercions/array-length reduction and table Fin indices). Every replacement changed source; failed objects/diagnostic sorryAx are excluded from accepted roots.
