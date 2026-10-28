# NCJ TX2 weights lane

Stage 0: frozen source inventory; U12/U13 OPEN. Budget 70 Kani, 80 Lean; one capped scope at a time. No release claim, shipped edits, push or merge.

Stage 1: NCJ_L001 proves tensor write bounds, unread frames and disjointness for widths 1/4/16, plus final width and dot caps. NCJ_L003 proves the emitted guard rejects wrong folds/S1/D. NCJ_L002 was a failed proof attempt (unfolding the discriminator was missing), replaced by L003. Standard axioms only in green attempts.

K002/K003 are the KMX pointer negative/positive controls; K004/K005, K006/K007, K008/K009, K010/K011 are guard positive/negative pairs. Relevant factors are arbitrary raw QM31 words; irrelevant fields are zero and remain a framing obligation. K001 failed compilation because my scratch archive omitted a frozen tools include; no proof credit. Frozen Cargo.lock and resolved graph unchanged in every Kani attempt. Stage1 patch records exactly the scratch-only overlay; no repository shipped file changed.

Setup corrections: initial Cargo archives omitted frozen workspace/path members and the tree-reference include. Metadata FROZEN_GRAPH/2 failed and FROZEN_GRAPH3 passed after unchanged files were added; the archive helper hit argv length before submission and was narrowed to the actual dependencies. These are worker-input repairs, not host infrastructure changes.
