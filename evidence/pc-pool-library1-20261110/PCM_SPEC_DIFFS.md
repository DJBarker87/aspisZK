# PCM source audit differences (specifications still DRAFT)

No row credit; target not yet established. Pool source is b936275465, crates/lock 4bb3b3f51e16.

- PCA_RowSpec_POOL_* and PCC_CHILDREN are schemas/drafts rather than full fixed specifications. They are not installed as CLOSED laws here.
- Deposit POOL:304/326 use the generic lane decoder/append/encoder. The deployed feature set does NOT select pair-forest-deposit-invariant-audit. Terminal POOL:312/319 DO select source-invariant/source-result-invariant bodies.
- POOL:339 allocates the common Box and statement Box before its final possible InvalidVerifierReturnData; POOL:319/326 allocate a next-lane Box before their encoder can reject.
- POOL:348 allocates metadata and infos Vecs, optionally grows both for the verifier checkpoint, allocates the decoded-result Box, and may shrink returned_data into a boxed slice. The Vec capacity representation is an explicit remaining adapter obligation; byte equality alone cannot discharge it.
- AccountInfo::clone is not an allocation. Its Rc-overflow abort is now named at clone sites. No native Rc count/drop frame is inferred from NLF; NKZ_OBLIGATIONS expressly excludes it.
- SDK data_len/data_is_empty and lamports use infallible RefCell borrows. Their conflicts abort, rather than returning AccountBorrowFailed. Lamport cells are separate from data cells.
- CPI-passed bytes/lamports/owners remain unconstrained by the reference runtime parameter. RuntimeCpiReadonlyEntry7 is PENDING/UNUSED. Counter/handle/clone frames remain native/representation obligations, not RuntimeCpiAccountView facts.
- RSL PoolLib is reused literally as PCM.SharedPoolLib. Pool guard-owner rows are not TAS verifier entry rows with coincident numbers; the eventual top skeleton must expose the Pool-to-verifier occurrence adapter.
- TX2:064 supplier is NMN_064.root plus NNC weak law/option B, never unconditional Root0. L154, Realizes, RZ-STATE and the split form are unchanged.

Draft corrections retained in history/receipts: the marker is 208 bytes; the withdrawal signer seed is aspis-pool-vault-authority-v1; the leaf sentinel is limb 7; all leaf error constructors are retained. These drafts are not frozen or accepted specifications yet. Failed elaborations are excluded; automatic sorryAx in failed compiler diagnostics is not an accepted root.
