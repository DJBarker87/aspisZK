# PCA CPI obligations

No native CPI bridge or failing control has run. E4 NOT MET.

Token site: pair_forest.rs:1170. Target is the EXACT transfer_plan.instruction (program id, ordered metas including flags, complete data), transfer_infos order token_start+[1,0,3,2,4], no signer seeds at this invoke, and exact Err propagation/no later Pool writes versus Ok continuation. No fixed token semantics or successful reply is allowed.

System sites: parent 1107/1145 through create_or_allocate_pda then create_or_allocate_pda_with_rent. PCA_SYSTEM_CPI_INVENTORY.json records the actual nested builder and runtime method occurrences; archived frozen child source is preserved for review. Their instruction/meta/data/infos/seeds/full reply and abort prefixes still lack certificates. This is more than one system CPI shape; it is not credited as one completed bridge.

Exact seeds at the parent: UTF8 `aspis-pool-root-page-v1`, lane_account.key bytes, eight little-endian page-number bytes (0 for genesis), one bump byte. PDA op38 remains quantified; no PDA value assumption. Native association to the SDK syscall still required.

Callee changes on passed cells are unconstrained. Parent-local data writes start only after token Ok and delta validation Ok. A system CPI can occur earlier and its effects/error prefixes remain observable in the parent state. The unpassed/caller-view interface is the PENDING PCA_CpiFrameCandidate; it has not been promoted to runtime trust. Guard/handle/metadata stability still needs SDK/ABI proof. RuntimeCpiReadonlyEntry7 unused.
