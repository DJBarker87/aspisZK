# Symbolic nonvacuity proof decomposition

The full successful path cannot be proved from selection alone. reference227
calls terminal_parts -> composition_parts, followed by equality_value and total
QM31 operations. composition_parts has amount rejection and transition rejection;
a successful witness must discharge both explicitly. Claim arrays and challenges
need not be numerically evaluated to show the remaining arithmetic terminates.

Needed bounds/loops:
- select227:84 steps, retained existing symbolic theorem.
- Selectors.expand: high64 from6 coordinates and low16 from4. Inner descending
  index invariant2*index<=N; outer remaining-coordinate invariant
  len*2^remaining<=N, coordinate+remaining=start+count<=10.
- active/pattern/evaluate_copy: bounded masks, literal pattern ranges and link
  indices. Their success proofs must use the constants' shape, not arithmetic
  evaluation of a1024-row selector.
- bounded_append_carry and transition: at most20 levels, carry<=20; successful
  witness must relate both frontiers, retaining equality/error paths.
- add_preweighted: per-chunk lengths<=4, output group index<24.
- sum_interval: interval endpoint within its array length.
- composition_parts: mask column<10; reverse folds start at24 and4.
- Poseidon helpers: constant array indices; prepared accumulation preserves nine
  independent matrix slots. Successful termination does not establish D188
  fidelity or deployed native correspondence.

All uses of an extracted function's meaning as Rust semantics are
reclassification within existing Charon/Aeneas tool trust. No fact is added to T.
