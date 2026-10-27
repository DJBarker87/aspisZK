# Root audit dependency obstruction

The exact Port5Q2_Prepared chain passed L001-L006. Further attempts restored
27 prior XRn dependencies, Op4P_Accepted, six Port5Q2_Checkpoint prerequisites,
and PAln_MatchingFacts. The root still fails at PAln_AlignedRead (L046), whose
11-source missing chain is being restored in L047-L057.

A compile-free traversal of FJv_Top source imports (coherent sources first;
canonical RPz5/RPz4/RPz3/RPz snapshots next) found 90 still absent objects among
6428 visited names, with 200 unavailable sources. This is an OVERAPPROXIMATE
source inventory, not a kernel dependency/axioms audit: some cached object's
source import list may differ from the available snapshot; standard/library
objects also come through Lean's builtin paths. XRo_ROOT_STATIC_INVENTORY.json
records every named candidate/path/hash, not an unproved claim of root closure.

After the already-running aligned-read chain, stop expanding this repair
campaign and retain the exact next kernel import failure. Building this broad
closure would consume the allowance intended for new association proofs.
Proceed to independent new XRo_Join_ carrier/scalar work, without claiming a
successful root audit. No alternate cached-object directory is added to hide
the missing coherent objects, and no shared cache is repaired.

L047-L057 all passed. Final attempted kernel audit L058 fails at
PAln_OpeningDecode, exit1, wall0.594310046s, RSS1520940KiB, swap0.
No fresh root #print axioms result is claimed. Budget now58/100 Lean,0/10 Kani.
