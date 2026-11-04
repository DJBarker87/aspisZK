# Domains and boundaries

Entry: valid Solana AccountInfo carriers and arbitrary instruction bytes, including rejected inputs; no assumption of acceptance or account count. Stage1 call site derives data=[3,10] or [3,11]; stage2 call site derives ASQ8 prefix. Exact key/owner/flags/borrows and payload identities must be established at each snapshot and decoder. Caller count checks establish 3 or 7 accounts before indexing.

NGL_B001 → NFW_: tx1 packet on SAME statement.semantic_public(), original public bytes, proof suffix [688..58295], split 10/11, SolanaDigest and deployed None; every required preparation/canonicality fact must be derived there.

NGL_B002 → NFW_: tx2_authenticated and tx2_common packets on SAME encoded statement, selected proof and stored checkpoint; no independently chosen accepted execution.

NGL_B003 → NGC_: checkpoint result length and canonical contents returned from tx1; source stage1 checks the length before copying.

NGL_B004 → lead: stage2 calls set_return_data([]) before snapshots. Existing RuntimeReturnData law for nonempty reply persistence does not itself license an exact empty-clear transition. Native source forwarding and an explicit runtime interpretation remain required; no ADDED-PENDING-LEAD assumption is used as a premise.

SnapshotError domain: AccountBorrowFailed or InvalidAccountData. ProgramError also contains BorshIoError(String); proving scalar variants cannot be reported as a complete arbitrary-ProgramError clone certificate. Snapshot source produces AccountBorrowFailed for both length/bytes on SDK failure, InvalidAccountData for bytes on rejected lengths. The SDK error characterization remains the accepted S2TrustedSdkBorrow interpretation.
