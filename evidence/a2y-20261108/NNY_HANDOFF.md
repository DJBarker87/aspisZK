# NNY A2 handoff (in progress)

Target: `RSL.TAS.NND_A2 (AspisR1.NNH_Run5bHost.S_host L0 copy std) NNH_Libraries.L NNH_Libraries.D NNH_Libraries.V0`. No term delivered yet.

30 scopes authorized; 0 Kani, 0 extraction. NNU and NNH overlays are reference-only. Own overlay: `/home/dombarker/project-offloads/codex-cx-a2-20261108/NNY_objects`.

Query coordination: NNX owns the generic query lemma per A12P X2. NNY will reuse it when available; no second generic proof is planned.

Y0 in progress: the existing `NNH_Stage2GuardedEval` already chooses `.error .Checkpoint` at off-domain 064 calls; NNY will use this support evaluator rather than the unguarded evaluator. Full audit pending.

target not yet established

Y1 shared API (checked through L010): `AspisR1.NNY_MerkleShared.NodeLeaf D H` is in NNY_MerkleAgreement. Its only fields are `node` on `MultiproofConePhysicalDigest.parts left right` and `leaf` on `Port4B_LeafCode.input kind opening`, equating `D.digest ()` to `ok (rawOracle H request)`. `tx2 env` discharges the instance from NNU_MerkleDigest. `endpoint` and `verify` in NNY_MerkleEndpoint/Verify transport binary accepted replies using only this agreement; no global digest law or byte-length restriction. Parent still in progress. NNX should import by reference after pins/accepted overlay export, not use drafts as credit.

Y1 substage: generic node/row/height/endpoint/verify, terminal constructor and terminal transport are checked; opening width, one active iteration and abstract loop induction are checked. Parent remains open pending the loop/tree composition. L004 memory-stopped concrete induction is retired; L009/L011 direct terminal rewrite class is retired. Exact failed sources are retained in attempt snapshots; no failed theorem is credited.
