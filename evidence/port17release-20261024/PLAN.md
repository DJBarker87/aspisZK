# Port17RELEASE compatibility and assumptions map (before compilation)

Assigned base aab7c6fe684835c47c5495287ced886dbd83e903; immutable A delivery a4fa5c5ab357a4f6732a3e053965640c90a0df1e (effects predecessor f27f2bf73b). No source adoption, shipped change, or ELF rebuild. Default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. These pins are context, not new identity gates.

## Before and proposed after (complete quantified interfaces)

Before: LocalBudgets rest w := ∀ {A : Type} (op : Call A) (H : Bytes → State), operationId op ∈ [3,4,6,7,9,10,11,12,17,19] → (eval H (rest op)).1.length ≤ w (operationId op).

After: ReleaseBudgets rest w := ∀ {A : Type} (op : Call A) (H : Bytes → State), operationId op ∈ [3,4,6,7,9,10,11,12,17,19] → ReleaseCall op → (eval H (rest op)).1.length ≤ w (operationId op). ReleaseCall constrains ONLY observer arguments of op6/op7/op19 to None; other calls have True. Prove all syntactically possible calls in tx1 Flow10/None and tx2_authenticated/None satisfy ReleaseCall, universally over all child returns. This is a program invariant, not a premise on an adversary or a changed Flow.

Concrete installation: Port9OR_Installed.implementation ops reserved unwrap (AspisS1TopPrepareCode.body base R B other). Consume A installed_count at arbitrary D/H/pub/proof/hash/scratch. Preserve A source/effects equality at its exact P3 dictionary; arbitrary D count is not arbitrary D native correspondence. Some stays delegated to other, never rewritten.

Residual producer interface: every delegated operation EXCEPT op7, restricted only to proven ReleaseCall domain. Weight op7 is 115; residual weights remain explicit. Driver conclusion intended 1161 + residualWeight, first reads Q+1161+residualWeight, two-pass total Q+2322+2*residualWeight. No claim residualWeight=0 without actual named helper installation and native assessment.

Retain arbitrary adapter, top ops, reserved, unwrap, base, R (decode/boundary/value), B (fromFn/mask/add/mul/terminal/circle/claims), other, D/hash, public/proof/input, oracle H, decoder, ByteProver and its original Q bound. All source/native association boundaries remain open, including numeric/Std leaves, SDK/account/abort effects, parser/query/root/transcript/terminal/nohit, StoredCarrierBinding, NativeBindings and release identities. Pure Result lifting is not native no-read evidence. No whole-output equality or whole-driver budget premise introduced.

## Validation sequence and budget

Source-only immutable receipt/source/object verification first. Reuse unchanged Port16 sourceOne/sourceTwo equality, cuts, weights, stages_eq and same saved Vec. New release-domain theorem, release costs, concrete preparation consumer, actual driver/accounting, one complete statement/hidden predicate/axioms audit. Maximum 26 new Lean attempts (250 inherited charged, ceiling 276); no Kani, heavy Rust/backend/extraction, or full frozen manifest. Host: independent 6G/8G/zero swap/64 tasks and full cgroup reservation below 55GiB; global lock outside 22:30–14:00 London. Local fallback only pinned warm imports, task outputs, atomic lock, -j1 -M4400 and aggregate child RSS hard stop below 8GiB. Never modify A live source or caches.
