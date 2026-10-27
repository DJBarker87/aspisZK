# Before and after

Actual adopted theorem:AspisR1.ARX_Root.deployed. Full source statements are
JGm_BEFORE_ARX_Root.lean.txt and JGm_AFTER_ARX_Root.lean.txt, byte-identical at
SHA256f3292a045b924fda8e23f13704d4fdbb6bdd73b3665c3abf0ad0f77025435405.
The selected ARX object is identical in070 and100; both print standard axioms.
Ledger method, SAME witnesses/guards/carriers and deployment rows are retained
verbatim in JGm_LEDGER_DELTA.json. Actual83T/11P/13G/0C; deployment-inclusive
distinct89T/28P/13G/0C, before and after. Removed/added/changed each0T/0P/0G/0C.

Local before: JGc_TX2_Obstruction70.BatchGoal was open for the installed model.
Local after, exact theorem JGm_TX2_Batch.source:

    ∀ {Hash} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash),
      JGc_TX2_Obstruction70.BatchGoal
        (JFn_HashBoundary.dictionary JFp_SHADigest.digest D) hash

The dictionary is explicitly specialized to the real SHA model; this does NOT
claim BatchGoal for an arbitrary digest implementation. Prepared, retained proof,
folded root, batch1, native Result and installed leaves are the SAME targets.
No successful slot/batch/finish/wrapper result becomes a hypothesis. Batch.native
constructs the three chronological slot returns on SAME successive scratch.
LocalFacts in Batch's JGm_TX2_Partial namespace jointly constructs the inherited
13 facts, three actual owned verifier returns and the native batch. Its reader
join retains Realizes SHA and exact SAME saved-byte equality explicitly.
This is fixed-input local consistency, not complete deployed non-vacuity or
accepted2. Finish, accepted1/SAME save, accepted2 and the full joint pair remain.
