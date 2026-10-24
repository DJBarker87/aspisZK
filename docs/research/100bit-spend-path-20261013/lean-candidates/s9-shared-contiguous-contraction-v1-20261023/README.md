# Contiguous source-order tensor contraction

PROVED: the existing generic4x16 tensor contraction applies to the exact contiguous64 indexing sourceIndex(slot,j), whose value is j+16*slot. No contraction algebra was re-proved. This is pure mathematics; actual source-read meaning is supplied separately.

The one missing project artifact was checked against warm Mathlib first, then the new bridge. Both targeted checks used H1/Max2/Swap0 and standard axioms only. No library build or R1 source/runtime claim.
