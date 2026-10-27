# TX1 ownership check against frozen authentication

Frozen `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:376-416` checks three accounts: distinct proof/public/checkpoint keys, readonly-buffer FLAGS on indices 0 and 1, verifier-owned writable checkpoint at index2, then zero bytes and content parsing. `require_readonly_buffer` in r1_pool_adapter.rs:202 has no Pool owner comparison. Thus JFv_World.e1 has no analogue of JGz_'s TX2 Pool-owner defect: all owners are the verifier, index2 is writable, indices0/1 readonly, and all nonsigner/nonexecutable. This is a source/tuple inspection, not yet full stage1 acceptance.

The TX2 corrected tuple must instead make indices1/2/3 Pool-owned (master/forest/selected), retain verifier ownership at checkpoint index6, preserve the same bank cell2 checkpoint lineage and proof account. JHb_ owns that correction. Do not change JFv_World or another worker's files. This job will consume only merged JHb_ sources, read-only.

These are fixture model statements; no shipped-source counterexample, native differential or source-to-ELF claim is inferred.

## Merged JHb correction inspected

Read-only research 98a9a2a326 carries JHb_World. Its TX1 slots0/1 are foreign-owned[85;32], readonly, nonsigning/nonexecutable, while its checkpoint cell2 remains verifier-owned/writable. TX2 snapshot slots1/2/3 use Pool[65;32]; slots4/5 use registry[68;32]; slot6 is the same verifier checkpoint cell2. JHb_Header.account is the physical public[976,1664) header688 followed by the SAME JFx proof. JHb_WorldBytes.inputs identifies the corrected physical public/suffix and checkpoint lineage. These differences require explicit transport, not equality of the old and corrected entries. JHc_CorrectedOwnership is drafted to check that transport and the actual readonly guards; no acceptance is inferred from it.

Correction to imprecise inherited wording: the JGz obstruction is the **Pool master at TX2 slot1**, not the readonly raw proof at slot0. Raw proof ownership is unrestricted. JHb's handoff still delivers no unconditional accepted2. See JHc_JHb_RESEARCH.json and the read-only snapshots. No merged JHb source was edited.
