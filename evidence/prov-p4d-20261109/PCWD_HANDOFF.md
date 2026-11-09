# PCWD_ handoff: phase P4d (reach check, S1ValuesOwnedModelV1 headline rows)

Target not yet established. Read-only analysis; no existing file, ledger row, trust row, RSL, contract or source changed. Nothing pushed or merged.

## Result: both roots UNLINKED

For `AspisR1.RPx_Deployed.deployed` (TX1:168/169/170) and `AspisR1.NHS_CheckpointPacket.source` (TX1:186), the constant-dependency cone (types and values) reaches all 16 `AspisS1ValuesOwned.*` constants, through `AspisS1ValuesOwnedInstallation.nativeValues/withValues -> expandValues -> values_owned_reference`. The cone contains no theorem whose type mentions both an S1-family constant and a constant named `*compact.expand_values` (B set empty, both roots), and no constant named `*compact.expand_values` at all. Blocking the B set therefore changes nothing; there is no path that passes through an equality.

Witness paths (PCWD_REACH.json): deployed -> FJv_DResult.Outcome -> ClaimsUnrolledSdk.sdkOps -> withValues -> expandValues -> values_owned_reference; checkpoint -> NHS_NFWObligation.source -> NHS_PrepareScratch.source -> nativeValues -> expandValues -> values_owned_reference.

The equality exists, outside both cones: `NGV_ExpandAssociation.result` (window: input <= 1856 bytes, aligned to 16, output = 2 * input) equates `NFU_Retarget.compact.expand_values` and `AspisS1ValuesOwnedInstallation.expandValues`. It is used by NHF_Expansions.construct (y1 window 464 -> 928) and NGV_RowPayload.construct. The module imports RPx_Deployed, so it is downstream of the deployed root. LIBC_ExpandValues speaks only about the NFU function (domain <= 1856 / 3712); NNH_Run5bCurrentExpand identifies op11 with the native wrapper at nativeValues by rfl and nothing more.

Missing: a theorem inside (or composed above) the headline statement that rewrites nativeValues/expandValues to the NFU function on the reached window, using NGV_ExpandAssociation.result.

## What ran
PCWD_L001 (combined import) exit 134, memory_exception at -M7000; cause a meta-program ownership defect (struct update copying a HashMap); shape retired. PCWD_L002 (import the two root modules, ownership fixed) exit 0, 47.0 s, peak RSS 6.68 GB, swap 0, caps 6G/8G, admission allowed, host scope count 1, disk >= 40 GB. No axioms printed: the file declares no theorem. Local type-check of the meta file with Lean 4.32.0 on a small root before the host run.

Limits: constant-level cone, not a semantic proof; stdout of S1_ENTRY lines capped at 400 (237 printed).
Files: PCWD_ReachMeta.lean (scope 1), PCWD_ReachMeta2.lean (scope 2), PCWD_launch.sh, PCWD_L00{1,2}/receipt.json and stdout.log, PCWD_REACH.json, PCWD_ATTEMPTS.jsonl, PCWD_CLASSIFICATIONS.json.
