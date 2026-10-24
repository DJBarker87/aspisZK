# ResourceAvailable retained failures

The audit-first receipt (source abaea0255b) records exit 1, wall
0.728165958s, RSS 177258496 bytes, swap 0. All 14 focused groups passed and
the complete original 15,015-event gate/input/report replay succeeded before
a new observer assertion failed comparing read_attempts. Cause: the new causal
adapter raised OSError(errno, recorded formatted error), duplicating the errno
prefix in str(error). Replacement uses the same recorded-error __str__ adapter
as the original replay, preserving original text; no error is dropped.
The changed observer audit and missing successful causal evidence justify a
new full causal attempt. No resource failure or cap increase occurred.
Primary fetch transport failures are retained in SOURCE-ASSESSMENT.md.
Old ResourceStat/ResourceHierarchy denials and failures remain immutable.

Audit-second (7ff57c86f2): exit 1, wall 0.839904583s, RSS 176865280 B,
swap 0. Focused groups, original hash/DENY replay, new ordered observer
comparison, and concrete ResourceActual 4 GiB arithmetic passed before
counterfactual enumeration reached an older failed capture with legacy=None.
The wrapper incorrectly attempted dict(None); it now passes missing evidence
through to the fail-closed evaluator without synthesizing visibility. The old
capture remains missing and denied. Added raw global duplicate/unit parsing
and delegation tests to cover source errors rather than accept overwritten
fields. These changes and missing final causal artifact justify the next run.
