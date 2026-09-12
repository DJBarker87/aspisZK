# Gamma challenge-input bridge — 2026-09-12

`lean/FSV8GammaChallengeInputBridge.lean` constructs the V8 first gamma
candidate input from the actual post-label-28 nonce transcript cut:
`List.ofFn afterNonce.digest ++ [1]`. It proves that this exact input is the
first query of `FSNonzeroQM31.candidateScript` and occurs in the candidate's
resulting chronological log, while the candidate run preserves the
post-nonce oracle prefix.

`gammaBoundaryConfiguration` uses that computed input as the V7
`OriginReplayConfiguration.transcriptDrivingInput`; fork output, post-fork
controller, limits, budget, and replay fuel remain explicit. Thus this leaf
constructs the driving input rather than recording a caller-supplied query,
but it does not yet prove that the V7 restoration `fixedFirstRunRecord` cut
selects this same source-history record. That history-to-origin cut, target
programming, and fork/resource instantiation remain open. No freshness,
success, acceptance, ROM, or probability claim is made.

Evidence: `results/gamma-challenge-input-bridge-v1/report.json`.
