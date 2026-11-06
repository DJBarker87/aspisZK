# Correction of the provisional guard diagnosis

The suspected emission mismatch was WRONG. The complete AdapterRwModel.stage1_owned body has442lines: its outer else at3075 performs the [3,11] comparison and repeats the entire caller body. The first body alone is not its full guard. NLD_Stage1Source also includes that second branch. No extractor/provenance defect is established by these native checks.

K002/K003,K006/K007,K008/K009 are retained without renaming: they establish the native duplicate-key rejection and fail a deliberately wrong InvalidInstructionData assertion at entry/process/stage1. The historical harness suffix model_control was an erroneous interpretation, not an actual formal-model assertion. Kani verdicts did NOT change. They are local native regression evidence, not an implementation/model counterexample.

L015,L018,L019 tried to prove a FALSE model-rejection statement and failed. Their error-recovery sorryAx outputs are excluded, never admitted objects or audit roots. NLQ_FrozenStage1Owned (uncompiled proposed repair) is RETIRED; its extra comparison was unnecessary. No existing proved module or shipped source changed.

NLD's handoff language about eleven rejection before guards must not be relied on. Frozen Rust AND the emitted model permit eleven through the early guard and may reject it earlier than tx1 on account/decode errors. The source-to-model fold must retain that second branch. The independently proved NLQ_Route theorem already includes both routes and is unaffected. Target not yet established.
