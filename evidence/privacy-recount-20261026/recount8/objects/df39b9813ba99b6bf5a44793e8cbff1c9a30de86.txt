# Input stage checked

At 44689, InputRelation31 establishes InputWitnessCore.Relation for arbitrary K
on a successful inner compiler return, Checked words, canonical snapshot frontier,
and a successful runtime selected-spendability check. The latter is discharged by
CanonicalInput31.transfer/withdrawal (44690), which extracts the actual common
runtime validator success from canonical-route compilation. No semantic input
relation is assumed by those canonical theorems. Both Result layers are retained.

The relation includes pair validity, selected-slot spendability, selected commitment,
first sibling, nullifier and 24-level membership. The earlier lane-root source link
is retained at structural (K-1 substitute) class, not relabelled as Kani.

CarryFrame31.frame (44692) preserves the frontier at/above the stop.
CarryStop31.stop (44694) computes stop as the bounded trailing-one count.
RecordAppendLift31.path_prefix/root (44696) lifts record appends to the semantic
path-prefix recurrence. These are intermediate append facts; AppendBinding is
not yet inferred. CarryMeaning31, OwnedCarry31, PublicCarry31, CompilerAppend31
and LateAppendRoot31 remain candidates until individually checked.

Receipt 44689 records a source-capture exception: the prelaunch commit failed on
an index lock, then the exact snapshot compiled successfully. The launch HEAD
is preserved, and the later source_capture_revision/blob proves the exact bytes
were committed. Validator explicitly checks that record; no unchanged replay.
All later launcher calls require the source bytes to match HEAD before launch.

No deployed premise is removed, added, weakened or changed. Admission is still
required at the honest-family endpoint until append, variant-output and transfer
sentinel are proved. The exact owner coverage sentence and V038/V045 remain
pending, in that order. The privacy target is not yet established.
