# Actual runtime candidate-list and joint-lane expansion bounds

For the actual successful initial/final GS calls, the image-and-distance-filtered candidate lists contain at most 112 entries. Filtering cannot increase the underlying recovered-root-list length. The actual joint-candidate family has at most 100 members, so expanding any selected lane before pruning produces at most 11,200 entries. The selected lane is tied to its actual successful call; the other 28 decoded lists remain arbitrary and may differ.

This reuses the already checked raw recovery output-length theorem and joint-family cap. It does not replace actual lists by sets or assume identical lane lists. Version 7 specialized all lanes to one raw list and is not the published theorem; version 8 corrects that scope.

Exact focused local/native receipts, source/object/import hashes, commands, revisions, exit status, wall time, RSS and standard-only axiom reports are retained. Native jobs used finite cgroup memory limits and MemorySwapMax=0. There was no package-wide replay.

These are concrete size bounds needed for polynomial extractor cost. They do not alone bound polynomial arithmetic, bit operations or the full extractor runtime, nor establish protocol/source soundness, privacy or the transaction release gates.
