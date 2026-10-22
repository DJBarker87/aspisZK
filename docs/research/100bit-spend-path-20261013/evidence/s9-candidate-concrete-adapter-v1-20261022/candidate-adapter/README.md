# S9 candidate helper adapter, attempt 11

Immutable source-only bridge revision. It changes only the six bridge proof expressions relative to attempt 10: each selected FieldOps application is parenthesized on one line and the `do` sequence uses an explicit semicolon. The generic `mapResult_bind_roundtrip` lemma still preserves all three Result constructors and keeps the selected operation abstract.

Generated Types/Funs and ExternalOps are copied unchanged from the previously checked adapter revisions. `check_adapter.py` verifies those source pins, the six concrete operation bindings, no proof holes/options, and source-only packet contents.

This attempt has not been compiled yet. Its predecessor attempt 10 failed at Lean parsing of multiline `do let` slot applications; see its retained evidence log. The next action is a focused central compile against the selected full profile and the green Types/External/Funs objects, followed by an axioms audit.
