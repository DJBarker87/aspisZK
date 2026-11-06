# PCA proposed returning-CPI frame

PENDING, not adopted. `PCA.PCA_CpiFrameCandidate` in PCA_CpiFrame.lean is a hypothesis of intermediate lemmas only. It says:

1. Data bytes, lamports and owner of each admitted account NOT in the passed AccountInfo list are unchanged on a returning invocation.
2. The caller view of each passed account equals the callee's final data bytes, lamports and owner.

The source's own uniqueness check and NIZ_LAYOUT.deposit_separate are prerequisites to using account-list exclusion as cell exclusion; entry admission alone is not reapplied at the CPI. The same identity must be carried through every child. Parent guard-token preservation is a separate SDK/native obligation, not smuggled into this candidate. Key/flag/handle frames belong to the SDK/ABI source correspondence and also remain unproved where needed.

No token semantics, system-program semantics, successful CPI, readonly-on-entry, rent realization, transaction rollback or post-CPI balance condition is assumed. Passed cells may mutate arbitrarily. Every returned error, abort prefix and later absence of Pool writes remains in the parent target.

Source basis for review (not an assertion that this runtime version is deployed): [Agave v2.3.13 cpi.rs](https://github.com/anza-xyz/agave/blob/v2.3.13/programs/bpf_loader/src/syscalls/cpi.rs), specifically translate_and_update_accounts, update_callee_account and update_caller_account. The translation and account-index mapping motivate clause 1; the caller update loop motivates clause 2. The required version/feature/deployed-ABI binding has NOT been established. This is a source-based inference to a candidate interface, not a proof or adopted trust row. A generic R could retain unrelated handles; the native association must select the deployed SolanaPoolCpiRuntimeV1.

The weakest view frame is used: neither complete NLF state equality nor guard-counter equality is included. If native SDK/ABI correspondence needs an additional frame, it must be reported separately rather than silently added here. Only the lead may adopt or reject the candidate; this worker stops the trust-addition line here.
