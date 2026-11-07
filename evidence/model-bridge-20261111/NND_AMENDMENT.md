# TAS amendment recovery

Base: 707f5eef5b5; WIP retained in 2d5b467717b. Previous attempts E001–E002 and L001–L030 remain charged (2/2 extraction, 30/300 Lean/link/audit, 0 Kani). Failed attempts confer no credit, including L021 recovery sorryAx; L024 supersedes it with standard axioms only.

Authoritative targets: evidence/top-assembly-20261107/TAS_Interfaces.lean lines 317–324, `RSL.TAS.NND_A1.stage1` and `RSL.TAS.NND_A2.stage2`. Both quantify c,a,env,o,r and require Exhibited, EnvRep, Ref, and o.exit = ret r. Conclusion is ModelRet at the SAME arguments, for Ok AND Err. Per-definition equality alone is insufficient. No global endpoint equality or abstract Ops compatibility may be promoted into a root.

Difference from the original brief: returned-arm direction and runtime oracle agreement are additional required deliverables; the old value/control links remain support only. Native1/2 remain the actual AdapterRw functions at sdk c; extraction by rfl does not supply these fields.

Historical AdapterRw parent: 81521c77f7 plus retained candidate overlay, not frozen4bb3b3f. NND_PROVENANCE.md retains the exact differing require_zero branch. All adopted comparisons must use fresh frozen emissions, including reused NMS/NMX/NMT/NMW receipts. No historical name-only equality is credit. Registry E001 fresh replay was checked; zero E002 failed to emit and is not a frozen emission.

Next stage: smallest uncompiled WIP NND_AccountCarrier and NND_Stage2Link, then runtime/environment returned-result transport, TX2 before TX1. Only NND_ modules/evidence are changed. Target not yet established.
