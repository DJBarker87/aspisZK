# Stage 5: both source batch checks on the same accepted pair

SdkD_CheckpointBinding carries the actual writer roots and all 22 raw query
words into the actual reader, even with different public/proof arguments.
SdkD_SecondCut/SecondRun retain the literal TX2 root-range/copy and batch
calls. SdkD_FirstModel/SecondModel transport each successful partial syscall
batch to the ideal indexed model, deriving root/node/query association from
source preparation/checkpoint provenance. SdkD_PairBatches uses the installed
source offsets from Stage 4 and obtains the original Tx1Q Run from precisely
the supplied SourceCuts. SdkD_ReplayPair.same_pair combines both on that SAME
witness into all six canonical indexed batch checks. SessionAPrepare remains
the permitted named preparation hypothesis. Repeated parents are included by
the indexed canonical replay, not deduplicated by an unproved equality.

Attempts 065..073 retained with source/dependency fingerprints, status,
wall time, RSS, swap and full axioms output. 072 was a local length-proof
error; 073 succeeds. All checked new theorem axioms are standard. No Kani,
shipped code, ELF, wallet, package replay or other worker changes.

This is a deterministic success-conditioned bridge, not yet removal of top
`authenticated_S1`. The remaining global source experiment must supply its
original commitment frames and a uniform query budget before the checked
SdkC_Replay recovery can discharge that premise. The collision loss is a
security-bound term: 6*(Q+1040)^2/256^32, equivalently
6*(Q+1040)^2/2^256; 1040 includes the appended canonical replay queries.

Attempt 074 was charged despite no Lean process starting: the immutable
source-code cache lacked S1CurrentPrepareCodeExactV1. The launcher correctly
reported FileNotFoundError, and was not changed. The independent generic
lowering was split to import only its actual cached dependencies (075), with
a successful focused compile. Those next-stage files are not part of this
stage commit.
