# SAME-eight-limb serializer association

XRs_ByteSteps.bytes32 (L028) explicitly expands widths 32,24,16,8,0;
there is no recursive toLEBytes simp. XRs_WordBytes.word (L035) proves the
exact byte-carrier equation for every U32. XRs_Serializer.same_eight_limbs
(L038) proves complete Result equality to the ORIGINAL installed sourceBytes
on the SAME eight coordinates, reusing the checked serializer P6 bridge.
No canonicality or success premise is added.

L027 was a pre-compiler import-resolution failure: the submitted import was
AspisR1WideToBytesIndexedCandidate (not an actual module). Launcher reported
FileNotFoundError, no compiler ran and no receipt was produced. Corrected to
the existing ToBytesGeneratedOutputV11 module in L028; launcher infrastructure
was not altered. L027 is conservatively charged to the 100-attempt budget.

A2 remains OPEN at queries, powers/cached-claim, scratch/errors and whole
narrowed prepare. All row statuses and headline ledger remain unchanged.
