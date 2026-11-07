# PCF correspondence status

No root CLOSED until the full Stream C gate passes. The count-model result is support only.

## POOL:364/365 account predicates

Native actual frozen functions are annotated only in the own external scratch tree. Their references are the value-only functions in PCF_AccountReference.rs; the native contract supplies the exact Boolean field/key/owner comparisons at the same arguments. Both result branches are checked on the complete ProgramResult: Ok(()) iff reference code=0; Err(Custom(c)) iff c equals the exact nonzero reference payload. Every other ProgramError variant falsifies the contract, so no ABI quotient or error-payload abstraction is used.

The nine payer/system projections correspond, in order, to processor.rs:138-150; the seven token projections correspond to processor.rs:335-340 and supported_program_loader:118-120. The references retain short-circuit error priority: InvalidPayer before InvalidSystemProgram. Native proof uses the actual supported_program_loader and PoolV1ProgramError::from, whose accepted PCB root packets must be re-gated with ledger23 before composition credit. No stub_verified, writable static, arbitrary operation dictionary, field product or new runtime law is used.

AccountInfo inputs are explicitly built from arbitrary key/owner arrays, flags, lamports and rent_epoch using the SDK constructor. Data is not dereferenced by either function. No account borrow, CPI, syscall, log or return-data call occurs on any arm of these source bodies. The contract has no modifies clause because there is no permitted mutation. General frame/carrier association remains a Lean obligation, including aliasing through RuntimeEntrypointAdmission-Pool; concrete fixture framing alone is never promoted.

## Extraction

PCF_E001 extracts exactly the same reference source bytes in a dependency-free reference crate with the NCO Charon/Aeneas pins. That crate has its own pinned manifest/lock and no feature-sensitive code. Every actual frozen-body Kani invocation independently validates the frozen release dependency graph, the complete resolved feature list, and unchanged frozen release Cargo.lock offline.

## POOL:332

PCF_Count.complete identifies source-ordered branches and PCA/PCC reference for every natural count and expected value. admitted_count proves the exact accepted split, fewer and extra retain both distinct errors, and result_state_effects carries the same state with empty ordered effects. This is a model proof, not a native certificate or accepted root.
