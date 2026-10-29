65952: pinned ExactTowerBase elaborated, but failed to create the .olean because
the task wrapper created only lean-objects/R1Z. Exit1, wall0:03.66,
RSS2583444KiB, swaps0, revision206e3173b3. No accepted object, zero credit.
Repair only the task-owned output-parent input: create the parent of the
requested private object instead of hard-coding R1Z. No shared runner,
reservation/barrier, limits, source or proof text changed. Retry65953 uses the
changed output-directory environment, under local-lean rule11 and the missing
evidence-artifact/environment exception. This consumes one extra Lean attempt.
