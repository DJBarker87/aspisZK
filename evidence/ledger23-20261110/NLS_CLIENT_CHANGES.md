# Owned client changes

Adapted ledger22 NLO clients into NLS-owned clients/workspace/cache. Shared reservation/launcher/monitor/shim untouched. Each scope has disk>=40GB and admission exit0 plus allowed:true before upload, one scope at a time, unchanged 180s timeout and 6G/8G/swap0/64 caps. Combined file contains module imports and headline axioms print only.

Native receipt validator reads NLH inputs only. Its first draft incorrectly required exactly one failed check for every negative control; NLH_K025 contains two: assert_eq panicking and the explicit inverted assertion. Correction validates exactly two there, exactly one elsewhere, all at assert_failed_inner and never an unwind failure, while requiring passing counterpart plus identical source inputs, frozen graph/lock/source/features and KMX patch. Existing retained validator accepted any FAILED result; this check is stricter. No native rerun or verdict change.

Required NLO_COMBINED_IMPORT.lean is a byte-identical receipt copy of the new NLS_COMBINED_IMPORT.lean source, compiled only as NLS_COMBINED_IMPORT under the assigned module prefix. NLO_COMBINED_IMPORT in its imports is the immutable ledger22 predecessor. Successors must import the NLS module from this job's export, following NLS_MODULE_MAP.json. No existing module is overwritten.
