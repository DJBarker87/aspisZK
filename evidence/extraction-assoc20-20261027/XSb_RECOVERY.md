# XRz evidence recovery

Read-only host access succeeded at 2026-10-27 19:50:54 UTC. The persistent cache exists and is retained. XSb_cache_start.sha256 records 102 retained object files, including all23 XRz objects. XSb_cache_recovery.json compares all predecessor start objects inside that cache with this recovered snapshot; this is a later snapshot, not a retroactive contemporaneous XRz END receipt. XRw objects outside this cache were not freshly hashed.

XRz L068 timing recovered verbatim in XSb_XRz_L068_recovered_time.log: exact target XRz_ParseAdvance.lean, exit0, wall1.0983969420194626s (time.log1.09s), peakRSS2657860KiB, swaps0. Original revision43dde414348c0268f72d470632f89f692b3bb05b with dirty source hash96f38c9be1cc9fcaec96e93781b9d2c0f7d02c1bc555c81f6c964304bd33cb50; original full receipt remains in extraction-assoc18. Original printed axioms: [propext, Classical.choice, Quot.sound]. This recovers historical evidence; it is not another compiler run.

XSb_PredecessorAudit.lean is the predecessor final-audit candidate copied byte-for-byte under this job prefix. It is UNCOMPILED and excluded from proof credit. XSb_L001 was admitted allowed:true AND exit0 but its source upload failed before process start. No co-import/root replay was completed. The attempted invocation configuration also omits XRz_objects from LEAN_PATH; a resumed configuration must include it before this candidate can work. No unchanged dependency was rebuilt.

No theorem or top premise is discharged by this recovery.
