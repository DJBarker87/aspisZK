# X1 interface finding (pre-parent check)

Read-only sibling NNY_MerkleAgreement defines NodeLeaf.leaf for every opening
without a length premise. NNY_MerkleShared.leaf later uses opening.length=832.
LIBC_CohortHash.backend only proves digest agreement under HashPartitions.Shape.
The empty opening falls outside that Shape: the physical input is
[[16,113],[],[]], but LIBC's flattened-message split returns
[[16,113],[],[16,113]]. Arbitrary partition-sensitive Env.sha256 can distinguish
them. Thus the requested universal NodeLeaf instance at LIBC_CohortHash.H is
stronger than the reached caller needs. Do not silently assume it or change H.

Proposed local repair: bound the shared leaf law to opening.length=832 (the
parent already proves this before leaf use), or give it a C04 Shape premise
and discharge that shape at every caller. No change to RSL or the headline
field is needed. The sibling module is read-only; NNX has not modified it.
The exact counterexample partition is scheduled in NNX_PartitionFinding.
Continue independent X3-X6 while the shared parent/interface develops.

Validation: NNX_L023 compiles empty_leaf_partition, exit 0, 25.8750316 s,
peak RSS 6,774,888 KiB, swaps 0; standard axioms. L019 was a source-only
redundant tactic error in the empty Slice length proof; fixed by removing
the tactic after `simp` had already closed the tiny goal. The theorem
establishes partition inequality; oracle distinguishability is its
mathematical consequence, not a measured runtime digest disagreement.
