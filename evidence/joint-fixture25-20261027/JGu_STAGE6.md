# All30 actual native leaf hash calls

JGu_M0Leaf00..09.source, JGu_M1Leaf00..09.source and
JGu_M2Leaf00..09.source now pass on actual fixed proof opening reads.
Modules: M0LeafSources00 in012,02/04/06/08 in071..074;
M1LeafSources00 in075; M2LeafSources00 in076. The source native leaf code is
used, with the concrete math-SHA adapter and existing named JGr_ hashes.
No new SHA blocks, rounds or digests are generated or reduced.

All input identities use32-byte selections and symbolic64-byte message
regrouping; the JFo read-return witness avoids transparent whole-buffer
normalisation. These calls are not yet a returned batch or wrapper success.

Every leaf cast/select/value/regroup/address/source theorem has its printed
standard-axiom audit in the passing receipt, with exact hashes, dependencies,
revision, target, command, wall, RSS, swap0, exit0 and unchanged caps.
077's iteration adapter failed solely on a missing dictionary import; its
recovery sorryAx output receives no credit.078 tests the explicit import.

No top premise is removed; FJv before/after statements and recount unchanged.
