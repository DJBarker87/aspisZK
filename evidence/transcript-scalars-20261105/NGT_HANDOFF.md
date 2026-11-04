# Transcript scalar samplers: working handoff

Status: TX1:169 scalar and TX1:170 scalar_k OPEN. No closure claimed.
Branch codex/cx-transcript-scalars-20261105. Frozen implementation revision
4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Headline
AspisR1.RPx_Deployed.deployed, frozen3. L154 remains a parameter; D188 narrowed.

Scope: exact three-digest block, scalar/scalar_k reduction and state/frame
association, runtime byte forwarding including arbitrary 928/2048-byte payloads.
NGQ owns queries and its unrolled block stages; read committed results only.
No shared or sibling worktrees are edited. Only NGT modules and this evidence
folder may change. No shipped Rust changes, wallet operations or push.

Plan: stage cuts with local records and matched failing controls; reuse CLOSED
sampler leaves only within their validated domains; emitted-body equality on the
canonical cohort; byte windows plus Lean induction, never dense whole buffers;
combined NGK import, standard-axiom raw audit, NFX scan; additive ledger admission
only after complete native/model/frame/calldata association passes.

Budgets: at most 80 Kani, 60 Lean, 1 extraction. One scope at a time (the stricter
local rule); 6G high/8G max/no swap/64 tasks; Lean -M7000; optimized Rust.
Admission needs allowed:true and exit0. Infrastructure faults are reported,
not repaired. Timed-out shapes are split, never replayed unchanged.

Retained trust: P1/runtime digest=H, returningValue on successful syscall,
P6/D188 option-A transport, accepted runtime/library/ABI/allocator/source-to-ELF
and cryptographic/privacy/two-transaction assumptions. No trust change proposed.
The 100-bit per-attempt release target is not established by this work.

Initial review: NGN_FAILING_STEP identifies missing complete native scalar and
runtime arbitrary-byte association. NFW bounded parts <=32 and sparse larger
windows do not fill that gap. Scalar has one absorb, one sampled digest, one
advance; reduction is a separate sampler callee. No SHA implementation will run
in Kani. Initial evidence scaffold only; validation and imported pins follow.
