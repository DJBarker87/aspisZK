# Remaining LIBB obligations

Target not yet established. No row is credited by LIBB; only the ledger gate may do so.

Modules6–11 are concrete: LIBB_PoolLib.library has all20 fields, LIBB_PoolLib.deployed fixes deployed IDs, LIBB_PoolLib.values instantiates all four NND returned evaluators, scanner_extent and LIBB_PoolNoWrite.laws compile. Pool fields require no new domain, Ops dictionary, success premise or trust row. The separate original supplier-cut association lemmas retain their original SAME-argument domains.

Module12 / V2Lib.tx2auth remains WAITING. VErr/debug/Root0 are fixed; the canonical auth field is not installed. Current support:

- LIBB_PartitionEnv uses the exact original Env.sha256 part lists for resume and reconstructs C04 node/leaf partitions (including truncated views) without assuming partition invariance for arbitrary Env.
- LIBB_EnvCommon.resolved proves SAME Result and all outer events from one native continuation, with reservation tags bound ONLY at reached calls. LIBB_EnvCommon.stopped/stopped_query preserve the independently stopped C04 prefix and pending request; no source failure or returned native reply is invented.
- LIBB_RecordRender proves exact ordered decomposition of the SAME native rich trace using closed detail laws. The intermediate child laws must be obtained from NMN_064.root/NLT_CompleteRoot.root, and runtime tag binding must come from the actual host representation. Neither becomes an own-input clause.
- LIBB_EnvValues supplies Functional/Returns for the resolved-only source graph. This is not the complete tx2auth law. Complete the source/native observation fold including all permitted independently stopped prefixes, prove the canonical full-field gate on Dom064, then register the unchanged NNC_ObservedLaw.w as the weak law for that SAME V0. Bind I.f064 in the integration job, not by choosing a native witness or empty renderer.
- LIBB_Tx2Domain.native preserves exactly proof57607/checkpoint1768/public≤1880/Root0 at SAME inputs; no parser/child-success or global Root0 premise was added.

Module13 / V2Lib bundle remains WAITING solely on module12. No parameterized or relational stand-in is delivered as complete.

These remaining obligations are Lean/model/runtime-representation work. Zero Kani/extraction authorization is not their stopping reason. No historical determinism-obstruction investigation is reopened. Read LIBB_FINDINGS.md for repaired elaboration shapes and LIBB_CLOSED.json for hypothesis classifications. Budget/accounting and raw audit completion are recorded in LIBB_VALIDATION.json.
