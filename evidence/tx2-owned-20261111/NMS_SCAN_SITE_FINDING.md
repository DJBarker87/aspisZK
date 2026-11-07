# Scanner allocation-site correction

Source review of frozen r1_pool_adapter.rs:780-806 found that the provisional NMS_RSLScan.raw places allocation after the entire scanner source returns Ok. That is not the actual allocation point. Rust allocates Box::new immediately after the candidate decoder succeeds (791-794), before the encoder, byte comparison and tag at 795-800. Thus a successfully decoded candidate with a later rejecting tag still reaches the Box site and can stop there.

NMS_RSLScan.raw_extent/extent are true only of their defined provisional model, not a source refinement. They are RETIRED SUPPORT, excluded from candidate/native instantiation and exports intended for the next parent. No row or native credit had been claimed. The failure is recorded rather than hidden by a theorem rename. NMS_ScanLength.proof_length and NMS_ScanScalar.proof_value concern the original CLOSED source and remain valid.

NMS_ScanSites.scan is the replacement, transcribed directly from the same CLOSED source with exactly one explicit allocation operation after decoder success and before encoding. `erases` checks its value projection against NFY_JHf_Scan.source. Its RSL interpretation uses Spec.alloc at that actual site, carrying only a prefix on failure. No timeout, heartbeat, memory cap or frozen source change is involved.
