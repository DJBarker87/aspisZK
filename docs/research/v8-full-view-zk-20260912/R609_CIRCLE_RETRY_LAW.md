# R609 circle retry law

R609 proves exact output-mass formulas for the pure circle-policy program when each sampler reply is modeled as an independent uniform response. For any attempt budget `n`, it gives the mass of a requested accepted point, the outer parameter-exhaustion error, and the inner challenge-exhaustion error. It specializes these results to the selected three-attempt policy, retaining the returned advanced state and both error outcomes in the program model.

The exact formulas are defined in `AspisV8R19.R609CircleRetryLaw`:

- `lambda = ((1 - (1 / 2^31)^8) / 2147483647)^4`, the mass of one canonical four-limb tuple in the independent-reply model;
- `retry = modulus^2 * lambda`, the mass of a rejected tuple;
- `retrySum 0 = 0` and `retrySum (n+1) = 1 + retry * retrySum n`;
- for any budget `n`, the requested accepted-point mass is `lambda * retrySum n`, outer error mass is `retry^n`, and inner error mass is `(1 - modulus^4 * lambda) * retrySum n`;
- for three attempts, the requested accepted-point mass is `lambda * (1 + retry + retry^2)`, outer error mass is `retry^3`, and inner error mass is `(1 - modulus^4 * lambda) * (1 + retry + retry^2)`.

The target is [`R609CircleRetryLaw.lean`](lean/AspisV8R19/R609CircleRetryLaw.lean). Its rejected-event identity imports R608's exact pure-policy event theorem. The canonical file is byte-identical to the green focused snapshot, SHA256 `35f70ea88f10c9a48b21c7a745424af261b882fb51ef6c548facc57407b0de47`; the focused check used source revision `e370c116ce66eac8b2cd114dd4c3f35bb5bb3983` and the R608 dependency hash `3d0783a2fa333b4d64a05c085ccaf587cf433bc347f9236a98ecd71de31a37c3`.

The focused Lean check exited 0 in 1.86 seconds, with peak Lean-child RSS 3,290,612 KiB and swap 0. It used the pinned cached Lean 4.32 workspace with `-j1 -M4500` inside a systemd user scope capped at `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

Complete `#print axioms` output:

```text
'AspisV8R19.R609CircleRetryLaw.outputMean_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R609CircleRetryLaw.outputMean_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R609CircleRetryLaw.outputMean_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R609CircleRetryLaw.independent_missing_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R609CircleRetryLaw.independent_retry_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R609CircleRetryLaw.independent_point_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R609CircleRetryLaw.selected_three_attempt_point_mass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisV8R19.R609CircleRetryLaw.independent_outer_error_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R609CircleRetryLaw.independent_inner_error_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R609CircleRetryLaw.selected_three_attempt_errors' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is an independent-reply law for the sampler program, not a shared-oracle law for the actual callback. It does not prove fresh squeeze-address conditions across retries, the complete native callback chronology, or end-to-end privacy or security. The first missing bridge is to account for repeated-address collisions and retry losses under one actual shared oracle, then connect the full callback's native execution to this program model.

All four focused attempts, including three failed proof iterations, their exact source snapshots, logs, and receipts are preserved in [`evidence/r609-circle-retry-law`](evidence/r609-circle-retry-law/). The first two attempts predated the local R608 source copy and have no recorded direct-import hashes; that historical gap is recorded in the manifest. The final two attempts record the exact R608 source hash.
