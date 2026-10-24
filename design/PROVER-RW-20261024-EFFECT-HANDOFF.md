# Stateful entropy: checked factoring and remaining effect boundary

Unmerged adoption candidate on `codex/cx-prover-rw-20261023`, continuing
`7db89a0216818294add9efa77101568aed1a3629`. No shipped source, feature, wire,
protocol, security-contract, key, or artifact changes. No merge/push.

## Exact extraction interface and transport decision

`effect/interface-inspection.json` inventories the **caller-005 executable**
`aeneas-b59d5188-lean432-extended-static`, not a different installed Aeneas.
Its backend source revision is `b59d5188c082f704a418c7cb4e52ad69328002d1`,
with dirty-source details and source/binary hashes retained. The existing
Charon input is `ProverRwCaller.llbc`, SHA-256
`4c8ccdd05650fdfa28280fae443328f1ae20d91f6a52b6c5dc735e70b99b31af`.
No new extraction or toolchain build was launched. Derived LLBC is over 5 MB;
only its hash/size and interface inspection are added here.

The emitted boundary remains
`Slice U8 → Result ((core.result.Result Unit getrandom.error.Error) × Slice U8)`.
`ExternalFuns.op129` has no world. Backend `FunsAnalysis` retains a `stateful`
analysis field, but `SymbolicToPureTypes.compute_raw_fun_effect_info` drops it;
the translated effect record carries failure/divergence/recursion only.
`Config.ml` and `Main.ml` expose no state-passing switch. The state-error
examples in `Pure.ml` are comments, not an implemented external interface.
This inspection supports **no usable implicit-world extraction path in this
pinned backend**, not a claim about all versions of Aeneas.

Proposed checked transport: reify the concrete entropy body's single `fill`
request, carrying its exact pre-call input and post-call continuation. First
check specialization to the existing pure emission in Lean. Interpret requests
against ordered tape/world state. To claim native correspondence, additionally
prove adequacy of this request semantics against the pinned source/LLBC control,
then carry that world through `RealR1_client`'s callback and the actual retry
owner. The pure specialization theorem alone is **insufficient**: its quantifier
ranges over fixed pure dictionaries, which the retained obstruction proves
cannot represent every admitted tape.

No arbitrary-world adequacy theorem is assumed. No new trust item is introduced.
D188's existing `AeneasExtraction` supports the existing extraction; it does not
automatically bless an independently constructed effect semantics or a backend
patch. Treating either as trusted would require a new lead decision. A checked
LLBC/source semantics bridge could avoid new trust, but remains unproved here.

## Established statements

New modules use only `R1Z.ProverRwEffect*`; all previous obstructions and
snapshots are unchanged. Exact statements are in the committed Lean sources.

- `EffectSource.staged_eq` factors the actual emitted iteration before/at/after
  its unique `fill`. `EffectTape.pure_eq` checks reification specialization for
  **every fixed pure external dictionary**, retaining failure/divergence.
- `EffectTape.step_served`, `run_tape` and `EffectOwner.owner_tape` establish the
  generic finite-tape interpreter and ordered reply conservation for that
  concrete factored control. The world carries the unconsumed suffix and the
  complete ordered `(input, reply)` history. An unavailable tape reply remains
  a suspended request, not an invented native entropy error; interpreter fuel
  exhaustion remains a retry boundary. `EffectControl` proves source-specific
  cap/OS-error laws and retains failed/divergent reads.
- `EffectNonzero.scan_fixed` proves the actual emitted OR scan symbolically;
  no concrete 32-iteration normalization is used. `EffectPrefix.install`
  explicitly supplies transparent `Zeroizing` new/deref/deref_mut/as_mut entries
  125–128; it does not assert their native contracts. `fresh_zero` proves that
  the actual pre-call input is freshly zero under that installation.
- `EffectRegression.zero_then_one` and `EffectOwner.owner_zero_then_one` prove
  zero-then-nonzero retry/success with both reads retained, the actual emitted
  continuation and an admitted public nonce. The former permits any nonce at
  the loop boundary; the latter checks the source nonce-admission predicate.
  Neither assumes retry/success equations or independent draws.
- `EffectOwner.pure_owner_eq` reaches the entire actual entropy owner.
  `EffectCallback.callback_eq` reaches the actual RealR1 callback, preserving
  the account callback's updated state and identity backwards continuation.
  `EffectRetry.client_retry` connects the **actual RealR1 caller** through that
  factored pure callback to the actual eight-attempt retry model. The per-attempt
  prover body remains the actual parameterized source body.

No old statement or security premise is replaced. Before and after, the
unrestricted fixed-pure-dictionary E1 refinement is false. The new equations are
`pureOwner nonce = emitted.generate_for_mask_nonce nonce` and
`callback account pureOwner state k = emitted.call_mut account state k`.
There is deliberately **no** equation replacing `pureOwner` by `worldOwner` in
that callback. `client_retry` uses the prior sampler/variant dictionary
installation; the world regression uses the four wrapper entries above. These
are distinct, explicit installation domains, not a single closed native instance.

Only mathematical OR fixed-point hypotheses are used by the generic constant
buffer lemma, and zero/one instances discharge them. E1, E2, realBad,
realSeedQueries, the adversary, joint L1/L2 observers, PrefixContract,
BodyContract and RunJoin are unchanged and not newly established.

## Remaining blockers and minimal recommendation

The arbitrary-world-to-native/source effect association is still missing.
The pure specialization proofs cannot discharge it, and the original
`no_retry_then_success` remains applicable. The native callback still invokes
the pure extracted owner; the world interpreter has not been installed into
its source semantics or threaded through the native retry owner. In particular,
no probability pushforward, bad-event law, retry-independence claim or L1/L2
observation transport follows from tape conservation alone.

Minimal next deliverable: a proved effect-reification adequacy theorem for the
pinned LLBC/source control, including callback entry/exit and world updates on
all failures/retries, followed by a checked state-threading transformation of
the callback/retry path. Its conclusion must preserve the same ordered source
observations for each tape, then transport the existing E1 experiment and joint
observers. It must not assume output equivalence as a field. The current
factoring, exact source continuations and regression are reusable proof inputs.
A hash/AST-text checker alone would detect drift, not prove this adequacy.

If the lead instead chooses an unproved effect-capable backend patch, that is a
new extraction trust decision and is outside this authorization. Explicit RNG
plumbing in shipped Rust is also outside scope, would invalidate native
identity evidence, require all three ELF rebuilds and adoption/performance
gates, and is not recommended as an unreviewed shortcut. No such action ran.
**Conjunct 1 and the security target remain unestablished.**

Validation details and final budget are recorded in `effect/summary.json` and
the focused audit receipt. Failed elaborations/compiler checks are retained;
none is accepted evidence. Existing runtime/ELF evidence is reused with its
original source assessment, not promoted to a new artifact identity gate.
No frozen manifest or native/runtime gate was run. Quiet-host timing is skipped
while peer capped workloads remain populated.
