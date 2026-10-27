# Generic comparator transport

Checked map_sort, key_stream and tie_transport in JGk_TX2_ComparatorTransport (001). The transport requires only comparator agreement on members; distinct keys discharge the position tie breaker. key_stream identifies the result using sortedness and a permutation, without reducing mergeSort.

JGk_TX2_OrderTools (003) proves lexicographic comparator transitivity, totality, antisymmetry, sorted-permutation uniqueness and symbolic height-group append. 002 was rejected for an incorrect Boolean-coercion simplifier; 003 uses decide_eq_true_eq. Rejected sorryAx diagnostics receive no credit.

Only subsets of propext/Classical.choice/Quot.sound occur in passing axioms. Exact source/dependency hashes, revision, command, exit, wall, RSS, swap and cap receipts accompany each attempt. No actual ARX_Root premise removed or changed; fixed-input instantiation and full non-vacuity remain open.
