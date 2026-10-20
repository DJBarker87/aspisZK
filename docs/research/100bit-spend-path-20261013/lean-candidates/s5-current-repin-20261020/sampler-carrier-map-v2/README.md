# Candidate ordinary sampler to Prepared carrier bounds

This packet proves that successful candidate `ordinary_sample` output maps fieldwise into the Prepared public carrier `PE` and then through the accepted `toClaimE` carrier map into `CE`, preserving all eight U32 coordinates. Each mapped coordinate is below `P`. The proof reuses the focused candidate source-output theorem and the checked Prepared carrier conversion.

The generic Prepared callback is still arbitrary in `PreparedModel.Boundaries`; this packet does not identify it with the candidate ordinary sampler. It therefore removes no generic callback premise by itself. Production equivalence, runtime adoption, and sampler distribution remain open.

The v2 NUC receipt is green with standard axioms only (1.906s, scope peak 377,217,024 bytes, swap 0; 1 GiB high / 2 GiB max). The first v1 attempt passed admission but stopped in runner preflight because the selected Prepared carrier object root was missing; no Lean process ran in that attempt. The exact failure is retained.
