# Root A handoff: concrete delegated producers

The control-partition consumer is now green: `Port16CUT_Driver.rust1161`.
It needs the actual installed delegated `rest : Implementation`, a concrete
`w : Nat → Nat`, and for each operation ID3,4,6,7,9,10,11,12,17,19:

∀ result type A, every op : Call A with this ID, and every oracle H,
length(eval H (rest op)).log ≤ w(ID).

Then prove 2*w3+w4+2*w6+w7+2*w9+2*w10+2*w11+w12+w17+w19 ≤115.
No all-driver bound, successful run, independent checkpoint, or replacement
Flow can serve as a local witness. The actual returned TX1 saved Vec feeds
TX2 in the accepted consumer. The reader/batch/writer owned costs are already
reused symbolically; no re-extraction or batch recurrence normalization needed.

Accounting consumers `Port16CUT_Accounting.budget/log_length` require the same
local producer facts plus the original unrestricted ByteProver Q bound. They
preserve the distinction between repeated-pass first reads Q+1161 and total
queries Q+2322. Existing physicality supplies the source-field invariance.

This worker made no A-tree/candidate changes and did not work on parser/prepare7,
powers17, sampler, primitive/S6/S10. Their frontier and other soundness/privacy/
release obligations are unchanged. Both deployed targets remain unestablished.
