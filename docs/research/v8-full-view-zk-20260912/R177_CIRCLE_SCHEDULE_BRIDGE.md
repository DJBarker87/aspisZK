# R177 selected circle sampler to existing schedule

`R177CircleScheduleBridge.pureBounded_model` proves that R172's current selected circle model equals the existing `SamplerCircleBridge.modelRun` result/error/state for every total H, starting state and attempt budget. `challenge_schedule_exact` composes this with the actual selected three-attempt circle sampler. Successful points, both exhaustion errors, retries and stopping state are retained. The model's trace is not asserted equal to the source's oracle calls.

The focused target compiled on the pinned Lean 4.32 cache with the required caps: exit 0, 1.59 seconds, peak RSS 3,733,192 KiB and zero swaps. All five complete axiom reports contain only foundational Lean axioms and, for the actual sampler bridge, the inherited opaque Aeneas formatting type. Both failed elaborations and exact source copies are retained; their `sorryAx` output is rejected evidence. See the [manifest](evidence/r177-circle-schedule-bridge/manifest.json).

Next: successful current circle canonicality, distinct second-point execution, and faithful pair/freeze chronology. The source fold/extend and error-return extraction frontier still prevents whole callback correspondence. Shared-oracle probability, privacy and soundness remain open. Verifier source, security parameters and CU evidence are unchanged; no CU or unchanged regression suite was rerun.
