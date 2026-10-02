# R216: current primitives with a fallible shared oracle

`AspisV8R19/R216ResultOraclePrimitives.lean` compiled successfully in the pinned cached Lean 4.32 workspace. For the actual current selected transcript, an explicitly constructed adapter to one arbitrary fallible flattened-byte oracle gives exact absorb and squeeze result/error/divergence correspondence. Absorb uses the identical flattened frame for short and multipart branches; squeeze uses the original state for both ordered calls. No hash totality, independence, freshness, or concrete backend law is assumed.

The adapter is explicit, so this does not identify the actual hash implementation with a random oracle. It extends the earlier total-byte-oracle correspondence to arbitrary `Result` replies; both source hash failures and divergence remain visible. No new schedule model is introduced.

Exact compile revision: `9f15ca80aee857bc21b28ceb9e63658c7578b7e9`. Exit 0; wall 1.45 s; child peak RSS 3,699,284 KiB; swaps 0. The 5/7 GiB scope has swap disabled. Both complete axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Source checksum, raw successful log, exact runner, rejected first draft and failed log are retained in [the manifest](evidence/r216-result-oracle-primitives/manifest.json). The wrapper's tiny cgroup peak is not the Lean child RSS.

First remaining proposition: Bind the actual callback chronology including captured gamma slice fold, vector copying, source errors, stopping and all calls; identify the concrete hash backend framing and shared-oracle law before any privacy or soundness conclusion.

Verifier source and parameters are unchanged. The retained 999,790 / 999,532 CU results were not rerun. End-to-end privacy and soundness are unproved.
