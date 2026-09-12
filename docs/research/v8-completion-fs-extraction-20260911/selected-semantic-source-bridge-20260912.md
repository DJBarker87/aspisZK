# Selected semantic source bridge — 2026-09-12

`lean/SameBodySelectedSemanticSource.lean` closes the purely functional part
of the two value bindings left explicit by `SelectedConcreteTerminal`.

The same-body source constructor writes the sum of the mask into fixed field
zero before entering `SameBodyRelation.produce`.  Consequently the existing
causal relation strategy retains its original fixing points: response zero is
fixed before alpha, `final256` before queries, and each later response before
its challenge.  The resulting `FixedFieldView.initialClaim = ∑ mask` theorem
is definitional and does not use verifier acceptance.

The terminal runner then projects the 84 semantic point claims from that same
word, invokes a fallible selected-terminal callback, and only afterwards
compares its result with the carried ten-round claim.  A successful run proves
the comparison; it is not represented by an assumed proposition.  Given the
direct equality saying that this callback invocation returned the reference
trace's final value, the bridge constructs `terminalBound` and feeds both
bindings to `bound_terminal_constructs_residuals_or_named_exceptions`.
`RepairHit` is retained unchanged, as is the explicit `FollowsPlan` premise.

The exact remaining premise is therefore the literal source refinement

```text
selected Pool pair-forest masked terminal callback
  (the 84 point claims parsed from this body, semantic point)
= some (the fixed masked-table reference trace's final evaluation).
```

This premise includes the compiled selector/semantic/copy evaluator, the
selected mask evaluation, public-transition error behavior, and the equality
between its point evaluation and the independently fixed reference trace.  It
cannot be discharged merely from a returned `some`, root agreement, or a
renamed acceptance predicate.

No local Lean result is claimed.  A direct leaf command was stopped after it
attempted a cold Mathlib clone in the isolated worktree (34.71 seconds, about
54 MiB maximum RSS, zero swap).  The new leaf should be compiled after its
existing `SameBodyAssembly` and `SelectedConcreteTerminal` artifacts in the
pinned NUC overlay; no full manifest replay is warranted before that leaf is
green.

## Literal callback audit

`lean/SelectedSemanticCallbackGap.lean` records the next exact mismatch.  The
literal `performance_verifier::semantic` execution projects indices
`271 + (i / 28) * 29 + i % 28`, calls the pair-forest selected masked terminal
with those 84 values and the already sampled semantic point, and rejects when
the returned scalar differs from the carried claim.  Inside the callback,
`terminal_parts` computes the equality-weighted theta composition plus the
`mu` and `mu^2` helper terms; the wrapper adds
`state_only_selected_mask_value + eta * original`.

The frozen Lean `realTable`/`maskedTable` has the same intended Boolean-row
formula.  Existing selected-evaluator sparsity theorems prove generic kernel
reorderings only.  They do not instantiate the current 57-block, 94-source-
lane, 136-Copy-link pair-forest callback, connect its 84 supplied claims to
the corresponding table MLEs, or cover its public-transition error result.

There is a second independent gap: `ReferenceTrace` contains degree and round
boundary equations but no table-evaluation equation.  The new leaf constructs
a valid trace at the all-zero point ending at an arbitrary requested scalar,
showing that terminal authenticity cannot follow from the record as currently
defined.  Thus the smallest exact interface has two direct equalities:

1. the literal callback returns the frozen masked table's MLE at the sampled
   point; and
2. the independently constructed reference trace ends at that same MLE.

`callback_exact_of_table_terminal` composes precisely those facts into the
earlier `callbackExact`; it proves neither premise and introduces no renamed
acceptance condition.
