# Stage 2: TX2 chronological splice

UNADOPTED frozen3 CANDIDATE; option-B owner decision pending. S2 OPEN.
`F3S_SecondSplice.split` derives from actual successful `GExq_SecondCode.code`
a reached checkpoint reader and batch1 with their exact ordered concatenation
as the whole TX2 log. No log-equality premise. The intervening liftResult calls,
including the final FinishOps return, are silent in this particular source
interpreter; this does not independently prove runtime syscall silence.

F3S_012: exit0, wall2.039138342s, peakRSS5237836KiB, swap0. Standard axioms
propext/Classical.choice/Quot.sound only. F3S_011 independently checks common.
F3S_008/010 are excluded failed reductions, corrected with the generic
F3S_Silent.lift_log and explicit monad-lift reduction, not an assumption.
All invocations use the unchanged S2W launcher and exact 6G/8G/Swap0/Tasks64
scope. Reused coherent SInt2 dependencies. Receipt records source revision,
hashes, dependency fingerprint, command and full axioms/errors.

Still open: exact containing-source splice with same-pair segment witnesses,
model equality, composed non-vacuity and raw join. No release premise, shipped
source, artifact or frozen2 headline changed. Artifact pins and scope remain
as recorded in F3S_STAGE1.md. No push.
