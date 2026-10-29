# Duplicate declaration census (in progress)

Input: worktree `/Users/dominic/ZK/.worktrees/pv-evhc`, branch `codex/pv-evhc-20261029`, HEAD `4318dfa7971c50aae74845a1488433d13f631385`. Read pv-common, r1p-common, local-lean and the full Security and proof discipline section before execution. User D530 supersedes any older shared-types proposal: the RPx_Deployed + NDR_CombinedAudit soundness closure and manifest cbd00ba4 remain unchanged. All host object directories and Stream A files are read-only. Only new inspection sources, scripts and evidence are written.

## Method

Read the constant tables in each resolved `.olean`, plus server/private parts for module-system objects. This never imports both project cones into one environment. The scanner emits module, imports, constant names and extra code-generation names separately. A later exact comparison uses elaborated Expr representations of types and optional values, with opaque/theorem values included. No normalization, unfolding, pretty-printer name shortening or namespace substitution is used. This is a syntactic identity census, not a semantic equivalence proof.

READY and its reconciled manifest determine first-root resolution, including namespace shadowing. Native scope 70751 rehashed all 16,583 objects and all companions, 33,182 files: PASS, 37.780224622 s, 43,940 KiB peak RSS, 0 swaps. See verified.json and native-70751/receipt.json. No objects were rebuilt, copied or modified. The native ID audit found only this job's own unlaunched configs in 70750–70796.

## Inspection failures retained

70750: first two-object reader preflight exited 139 after writing its first row, 3.981105678 s, 1,538,880 KiB RSS, 0 swaps. The unsafe reader freed mapped data while local ModuleData references were still live; this is an inspection-script lifetime error, not a Lean theorem/extraction disagreement. Replacement 70752 moves serialization into a noinline function that returns only the compacted regions, then frees them after all ModuleData references have gone. No unchanged failed source is resubmitted. All runs use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and Lean -M7000. No 16 GiB scope, Kani, package rebuild, or consumer replay is authorized or performed.

No theorems are added. `#print axioms`: N/A for the object reader and native hash audit (no theorem elaboration or kernel claim); runner raw axioms arrays are preserved in receipts. Privacy endpoint premises are unchanged; target not yet established.
