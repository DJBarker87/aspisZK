# Compiler-return and selected-i dependency record

The exact return goal remains `@PV_Src_NativeInput.run E_shipped shipped i = ok (.Ok i.compiled)` at the actual selected record i. `run_update` is not success: the supplied Input.compiled field is ignored by the compiler.

Current checked source subresults: D287 records/CopyRecords returns, root helper/source cells, selected input leaf and membership path, record nullifier/recipient/change; runjoin17 production nullifier and output pair. Remaining compile guards include real late_append (OwnedTree validation/carry/reconstruct, complete afterstate), CopyRecords.banks construction and 57-block source `validate_forest_poseidon_rows`, and final returned trace/payload association.

The five D287 candidate files contain only numeric output-pair/append single-round certificates. No bank-validation candidate exists in that directory. Passing their cells does not prove the validator, compiler or whole selected transition. BankRow17 is a new candidate for the row checker completeness step; its actual Vec-read premises must still be established for each bank.

InstalledFamily.Selection.selected and publicRecord are explicit unconstrained data functions; no concrete deployed selection is fabricated. A compiler equation for an arbitrary new Input carrying a chosen payload would not provide its association to the actual selected i. After the return equation: prove full transition equality including frontier and snapshot, then deployed PublicBinding. Only afterwards construct P∧hypotheticalT. None of these successors is inferred from source digests or attempted ahead of the prerequisite.

Ledger: V152 public_eq, V153 build_eq, V154 transport_eq still REDUCED, not removed; V045 deployed source association, V038 agreement and V047 native fibre association remain. P={source public binding,trace} unchanged; deployed P OPEN; records2/8/6 unchanged. Endpoint premises removed/added/weakened0/0/0. T exactly entropy_law,entropy_kernel,observation.
