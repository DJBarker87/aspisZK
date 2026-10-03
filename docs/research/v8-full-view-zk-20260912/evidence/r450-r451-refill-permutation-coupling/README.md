# R450–R451 refill and stopping permutation component

This component joins the saved R450 refill-permutation run with R451’s stopping-count core and permutation theorem. The preceding R448 refill-source and R449 block-permutation packages are linked below rather than duplicated. The successful source snapshots are byte-identical to the promoted Lean targets.

R451 relates the source scan’s stopping count to the masked words and proves invariance under a word permutation that fixes the rejection sentinel. R450 relates the index-8 refill calls, result, carry state, block, and stopping index under the corresponding block permutation. Its adaptive-oracle prefix preservation theorem has an explicit `Fresh` premise; this component does not prove that premise for every actual campaign prefix.

Two earlier R451 drafts are preserved as rejected history: both hit Lean’s kernel excessive-memory error under the same 5G/7G/zero-swap caps. The replacement compiled under those unchanged caps. No higher memory cap was used.

The first remaining obligation is actual campaign-prefix freshness/unreadness and its composition with the entire four-limb distribution. This component establishes neither whole-program freshness nor four-limb joint uniformity. Run `python3 verify_evidence.py` here for a read-only integrity check. No compiler rerun was performed.

Linked evidence: [R448](../r448-refill-source-limb/README.md), [R449](../r449-block-permutation/README.md), and the existing [R447 chain](../r447-source-initial-block-law/README.md).
