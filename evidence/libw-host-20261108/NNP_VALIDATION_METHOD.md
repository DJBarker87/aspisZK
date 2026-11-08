# Validation method and provenance

Every submission uses fresh host scope-count, disk and reservation checks in
NNP_run.py, followed by the unchanged copied S2W_run_host.py. Admission requires
exit0 and allowed:true. Limits are6G/8G/swap0/tasks64, Lean-M7000 with async=false;
180-second scope-command timeout stays fixed. Existing LIBB_L344 path order is
preserved. Private copied LIBB_objects precede its unchanged dependency chain;
private copies of merged NNH objects and its two read-only seed paths are added
AFTER the original chain. Direct imports and selected Aeneas/AeneasMeta objects
are hashed on every attempt. Final selected full closure is pinned separately.

NNP_L013 ran the metadata scan in the Lean interpreter. It stopped with
'excessive memory consumption detected at interpreter' before producing scan
rows. No scan credit. The implementation shape was changed to native C:
NNP_L014 emits C for the already-successful NNP_Scan utility (missing codegen
artifact, not an unchanged failed replay), NNP_L015 links it with-O3. NNP_L016
runs the native metadata scan, then two raw-axiom groups sequentially inside
ONE scope; per-step GNU time receipts complement the outer scope receipt.
No increased memory/timeout or second interpreter run.

NNP_Scan retains NFX_Driver's referenceNames (including recursor reduction
rules and metadata), sameDeclaration, serialized-declaration owner comparison,
and checked-private-environment traversal. It checks dangling declarations and
references and incompatible duplicate owners for every loaded module. Cached
replicas with identical declaration shape are reported separately exactly as
NFX does. The independent expected-import-table comparison is not part of this
requested check; actual imported tables and selected hashes are retained.
NNP_SCAN_REFERENCE.txt pins the source used for the adaptation. The scanner is
a validation utility, not a new soundness theorem.

Raw ax2 is the existing LIBB_ProofDriver binary, byte-pinned to LIBB_L059
(ae808f235ba0735d10b204e7f96476f0fd386dcc00e90337d24eaeb8f6ad416c).
Its immutable Lean driver source is NNP_RAW_DRIVER_SOURCE.txt. The kernel-graph
walker uses checked-private declaration type/value references and the
constructor closure of the reused LIBB raw audit, not imported axiom caches.
Each result must match collectAxioms and contain standard axioms only. Active
root lists are committed in NNP_AUDIT_ROOTS.json; the retired failed module is
excluded. Output logs and reachable-name files are evidence, never proof inputs.

No full frozen-manifest replay or ELF rebuild is justified by these evidence-only
changes. Historical release pins remain inherited, not newly reproduced.
