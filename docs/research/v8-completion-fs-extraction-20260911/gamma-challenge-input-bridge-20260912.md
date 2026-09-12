# Gamma challenge-input bridge — 2026-09-12

`lean/FSV8GammaChallengeInputBridge.lean` constructs the V8 first gamma
candidate input from the actual post-label-28 nonce transcript cut:
`List.ofFn afterNonce.digest ++ [1]`. It proves that this exact input is the
first query of `FSNonzeroQM31.candidateScript` and occurs in the candidate's
resulting chronological log, while the candidate run preserves the
post-nonce oracle prefix.

`gammaBoundaryConfiguration` uses that computed input as the V7
`OriginReplayConfiguration.transcriptDrivingInput`; fork output, post-fork
controller, limits, budget, and replay fuel remain explicit. Under the
explicit premise that the corresponding adversary query is in the V7 origin
history, `fixedRecord_q1_contains_gamma` places it in the constructed
`fixedFirstRunRecordFromOrigin.firstRun.q1` and identifies the driving input.
The history-to-origin membership premise, target programming, and
fork/resource instantiation remain open. No freshness, success, acceptance,
ROM, or probability claim is made.

Evidence: `results/gamma-challenge-input-bridge-v1/report.json`.
