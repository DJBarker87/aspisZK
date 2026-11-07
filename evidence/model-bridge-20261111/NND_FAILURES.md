# Excluded attempts

L002: inspection used unknown U8.toBitVec/U8.val; actual carrier is UScalar.bv. No theorem.

L003: clipped column68 indentation causes Lean errors and recovery sorryAx; excluded completely. L004 uses token-identical repaired whitespace and no axioms.

E002: actual frozen require_zero cannot emit under pinned Aeneas: Not_found in InterpLoops loop-context join. No native result. No retry; extraction2/2.

Resume failures: L031 Vec.deref carrier reduction (fixed L033); L034 nonexistent Option.toExcept (fixed L035); L037 tactic alternative parser and L038 recursive macro declaration order (fixed L039). All failed outputs, including recovery sorryAx, are excluded. These are elaboration repairs; no timeout/memory failure was rerun.
