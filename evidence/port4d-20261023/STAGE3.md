# Row meaning and current finish round

`Port4D_FlushRows.accepted_rows` gives exact canonical row contents for the
current deferred parent; `accepted_field` proves its output field list equals
the actual raw prefix field list without raw lane bounds. `lower_value`
requires native value agreement only at reached indices. `materialize_fields`
preserves rhs, power and next of the actual query-loop result.

The current release Rust finish_relation_round was extracted with Charon and
Aeneas (charon001: exit0,138.684548s,RSS543408KiB,swap0;
aeneas001: exit0,1.197818s,RSS62128KiB,swap0). Time was optimized compilation
and focused MIR translation, not arithmetic elimination. The exact raw output
is retained as current-round/Funs.lean.txt; templates are not imported.
`Port4D_Round.round_small` proves checked/wrapping index agreement only for
round<=1. `parent_eq` installs THIS current round into the current parent and
normalizes it to the retained complete control, for either fold branch.

Accepted lean009(row meaning),011(pairing adaptation),014(current round):
exit0,swap0,standard axioms only. Exact targets, revision/source/dependency
pins, timing/RSS/axioms are in receipts. lean010 did not enter Lean (missing
historical pairing object); Port4D_Pairing is the checked replacement using
Port3 control. lean012 had syntax/name errors and a heartbeat timeout;
replacement isolates the actual state and marks run22/value/basis irreducible.
lean013 was an excluded attempted definitional equality; lean014 replaces it
with explicit bounded arithmetic laws. No caps were raised or failed inputs
rerun unchanged. These are focused development results, not release replay.
