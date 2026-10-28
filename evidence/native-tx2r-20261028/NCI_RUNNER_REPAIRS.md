# Own input repairs

NCI_K001 did not reach reservation or submit Kani: the adapted own wrapper retained the predecessor date 20261027 in B. Both preflight logs show own-path FileNotFoundError, not an infrastructure fault. Corrected to this lane 20261028 (rule 11). No overlap with L004 scope occurred because K001 never launched. The draft raw-reader precondition was also reordered to bound start before any checked addition; no native attempt had run. The later job allocation is 70 Kani/80 Lean, superseding the earlier total; runner enforces that final allocation.
