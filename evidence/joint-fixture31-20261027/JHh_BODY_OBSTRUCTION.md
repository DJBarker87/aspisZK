# Exact body-identification obligation

Checksum equation is `JHh_SHARealization.checksum`, proved independently by
`JHh_ChecksumEquation.source` from retained `JGz_ChecksumDigest.source`.
It hashes `JFn_HashBoundary.checksumParts`: the domain and retained1736 bytes.

The actual writer hashes `checksumParts body`, where body is constructed
from the SAME preparation and final flushed accumulator as the actual TX1.
`JHe_SavedWitness.inhabited` proves that call and its image. There is no
logical route from length1736 and header16 to body identity. SHA realization
can transport the checksum ONLY after actual body identity.

The inherited query theorem `JHc_QueryPost.source` concludes next10,
weights length64, variantS2, rhs canonicality and power canonicality. It does
not conclude final rhs=JFq_Rhs.scalar, power=JFq_Power.scalar or
flushed=JFo_Weights.value. These are necessary actual-run byte-identification
obligations, beyond the prepared state identity supplied by JHe. They cannot
be replaced by a successful reader of an independently supplied checkpoint.
No body identity field, accepted1 field, or output identity field was added
to the SHA class. No assertion that body identity is false is made.
