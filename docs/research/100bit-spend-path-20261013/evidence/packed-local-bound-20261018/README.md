# Actual checked packed-local bound

`external_local_limb_bound_success` proves the actual generated `EXTERNAL_LOCAL_LIMB_MODULUS_BOUND` operation succeeds and returns the checked U64 value 7*P. It reuses the current cast-value lemma and actual checked multiplication, with no assumed source success. This is a leaf of the pending full external-local packed caller proof.

The changed v2 focused NUC run passed with one standard-only axiom report, GNU-time elapsed 1.95 seconds, peak RSS 3,986,420 KiB and process swaps zero. Exact source/output/import hashes, compiler/command/environment, source baseline, pre-admission reservation and live watcher observations are retained. Job caps stayed MemoryHigh4GiB/MemoryMax4608MiB/MemorySwapMax0. The task-local reviewed reservation ceiling was54GiB, with fresh total53.5GiB and MemAvailable above50GiB; no watcher abort occurred. The original project-wide 50GiB guard was not edited.

Rejected v1 is retained. Its literal cast value did not close by reflexivity, and the irreducible source definition needed explicit unfolding. V2 uses the existing cast lemma and unfolds that source leaf; no resource cap was raised. Remaining callback/loop/raw packed callers and end-to-end security/privacy remain open. No runtime source/artifact changes are claimed.
