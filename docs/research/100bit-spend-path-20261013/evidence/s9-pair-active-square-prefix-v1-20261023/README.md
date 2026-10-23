# Pair active-body square prefix to source cut

This proof starts from one successful generated Pair loop-body call and the same `next = some side` witness. It extracts the actual Pair body prefix, derives canonicality of the selected extra seed and its first two concrete QM products, identifies the later array-selected value with that same q² value, and derives canonicality of q⁴ and q⁸ from the same successful square operations. It then proves the exact source-cut square results for q²→q⁴, q⁴→q⁸, and q⁸→q¹⁶.

The sole semantic input is canonicality of the actual selected `extra[side]` read mapped to the P6 carrier. No ap0/ap1 canonicality is assumed or inferred here because the square prefix does not read those arrays. The statements are limited to the generated body’s square prefix; they do not establish the later mixed terms, entire body/loop refinement, or a deployed-binary refinement.

Central Lean exited 0 in 33.219 seconds, peak aggregate RSS 3,273,900,032 bytes, zero swaps. Both exported theorem reports use `[propext, Classical.choice, Quot.sound]`. Full source/object/controller/profile/preflight/closure provenance is retained, but compiled objects and the large closure manifest are not included.
