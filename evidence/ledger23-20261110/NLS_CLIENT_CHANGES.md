# Owned client changes

Adapted ledger22 NLO clients into NLS-owned clients/workspace/cache. Shared reservation/launcher/monitor/shim untouched. Each scope has disk>=40GB and admission exit0 plus allowed:true before upload, one scope at a time, unchanged 180s timeout and 6G/8G/swap0/64 caps. Combined file contains module imports and headline axioms print only.

Native receipt validator reads NLH inputs only. Its first draft incorrectly required exactly one failed check for every negative control; NLH_K025 contains two: assert_eq panicking and the explicit inverted assertion. Correction validates exactly two there, exactly one elsewhere, all at assert_failed_inner and never an unwind failure, while requiring passing counterpart plus identical source inputs, frozen graph/lock/source/features and KMX patch. Existing retained validator accepted any FAILED result; this check is stricter. No native rerun or verdict change.
