# Symbolic contiguous source-sum transport

This generic algebraic transport keeps all source values as opaque parameters and reuses the existing checked4x16→64 contraction. It does not assert actual source operands already match the matrix or flat function: those explicit pointwise hypotheses must be proved by the caller consumer.

The one changed target passed on the same warm pure Mathlib/contiguous-contraction cohort, H1GiB/Max2GiB/Swap0/M4400/j1, standard axioms, no dependency rebuild. Exact source and validation are pinned below. No implementation/security assumptions changed.
