# Joint fixture16 progress

S2 OPEN; target not yet established. Branch codex/cx-joint-fixture16-20261027
(the supplied 20261026 suffix differs from the existing assigned branch).

Initial closure: 4821 selected modules, no missing objects. Reused the coherent
SInt2 cache with d18 v5 before aspis-joint. No package replay.

## Mask model transport

JGd_MaskModel.source derives actual retained-carrier mask success, canonicality
and its exact symbolic value from canonical inputs. The unchecked JGb model
comparison failed because definitional equality unfolded tower addition,
multiplication and the degree-26 power. Making only these operations locally
irreducible lets Lean compare their operands without evaluating the power.
This is a proof elaboration change; no source/model/trust boundary changed.
Attempt007 passes; attempts001–006 retained, excluded from validation. No failed
source was rerun unchanged and no heartbeat/recursion/memory cap was raised.

This does NOT yet prove the real-byte numeric mask value, actual terminal
value, final masked equality, preparation or accepted wrappers. No vacuity
finding. No top-premise removal credit.

All attempts use the existing host admission and launcher, one scope at a time,
-M7000, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64. No shipped source,
other prefix, live worktree, key or artifact changed; ELF rebuild not triggered.
