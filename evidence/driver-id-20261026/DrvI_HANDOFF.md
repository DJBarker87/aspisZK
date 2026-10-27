# Driver identification handoff

Branch `codex/cx-driver-id-20261026`. **L160 remains OPEN; target not yet established.**
Checked counterexamples prohibit inferring identification for the arbitrary
Implementation quantified by EndP from D188/P6 alone. They do NOT refute
existence of a compatible concrete implementation. No concrete carrier bridge,
AuS1 finish integration or deployed-source identification was established.

## Before / after statements

Before: `EndP_Headline.deployed_headline` takes arbitrary `adapter`, `impl`,
`Digest32 Hash`, `hash`; `driver_physical` proves Physical for every such
instance. `CPhy_Physical.accepted_pair_unified` fixes a different, concrete
SDK installation and its SolanaDigest at Unit. D188 associates native entry
functions and digestSource with that SDK; it contains no Implementation
parameter. EndP's GExp current/stage/digests are also separate parameters.

After (checked):

* `DrvI_Installation.sdk` literally names CPhy's dictionary. Its
  `same_batch_dictionary` proves equality with Op5T_SamePair's dictionary,
  without a compatibility hypothesis. Its `digest` is that SDK's SolanaDigest.
* `installed_split` / `installed_call_success` prove the actual installed
  stage op16 returns `ok 10` without queries. `silent_not_installed` proves
  an allowed typed Implementation disagrees at that very call.
* `DrvI_Counterexample.no_universal_identification` proves, for every SAME
  digest/hash/semantic/pub/proof and any fixed source Program and H,
  `not (forall impl, eval H (stages impl ...) = eval H source)`.
  Explicit witnesses are silent divergence versus one oracle ask then the
  same divergence. Their stage verdicts are both false; traces have length
  zero and one. Full Program identity is therefore impossible too.
* `DrvI_SourceCounterexample.silent_driver` proves the whole arbitrary driver
  returns `.done false` on ALL Inputs, independently of decoding. It is still
  Physical. `accepting_source_differs` proves that any source which accepts
  an input in H differs from this driver on that same input.

These conclusions preserve all byte carriers, the digest, the oracle world
and the existing definition of Physical. No model or source was weakened.
The incompatible instance is explicitly arbitrary, not claimed to be the
installed implementation. This is a counterexample to universal arbitrary
identification, not a counterexample to an existential bridge construction.

## Ledger delta

| Row | Before | After |
| --- | --- | --- |
| L160 | Driver/deployed-source identification open | RETAINED |
| Other rows | Existing status | Unchanged |

**Premises removed: none.** No source/extraction/runtime/P6 association is
proved by these counterexamples. No cryptographic assumption is introduced,
discharged or renamed. The only positive installation result is the checked
batch-dictionary equation; it is not whole-driver compatibility.

## Non-vacuity and success conditioning

`DrvI_Audit.nonvacuity` explicitly checks a Physical accepting constant source
and a Physical rejecting driver, and their inequality. This model has no
acceptance assumption and is not claimed to be an actual native accepted
fixture, nor joint inhabitation of the retained deployment premises.
`installed_call_success` is an actual successful installed op16 value,
without an impossible accepted-run premise. The prefix counterexample checks
both rejected executions, so equality of verdicts does not erase oracle reads.
`accepting_source_differs` is expressly success-conditioned on the source;
it does not assume or manufacture a native accepted pair. No soundness,
probability or collision bound is claimed from these statements.

## Validation and exact evidence

5/100 Lean attempts; 0 dependency builds; 0/0 Kani. Four pass. DrvI_001 is an
excluded development elaboration failure (`query` instead of actual `ask`);
its partial declarations/sorryAx output are NOT evidence. Changed source
passes DrvI_002. No timeout, memory kill, cap increase or unchanged rerun.

Unchanged S2W launchers in the coherent SInt2 workspace were reused. Every
invocation was one module via lake env lean, -j1 -M7000 -DElab.async=false,
inside MemoryHigh=6G/MemoryMax=8G/MemorySwapMax=0/TasksMax=64. No infrastructure
was written or changed. Two other populated 8 GiB scopes were observed
initially; final inventory shows only init.scope. No other job was touched.

Each DrvI_NNN/receipt.json records exact target/command, source revision plus
source SHA, direct dependency hashes/fingerprint, exit, wall time, peak RSS,
swaps, cgroup limits and full printed axioms. Stdout and time logs and exact
source snapshots are beside it. DrvI_FINAL.json aggregates these fields and
checks each final module matches a passing snapshot. DrvI_005 audits all 14
new theorems: only propext, Classical.choice, Quot.sound. Final audit exit 0,
wall 1.965949343s, peak RSS 5261236 KiB, swaps 0, revision anchor 2b13dc9823
plus exact new source SHA. No package/full manifest replay. No release claim.

No shipped/cfg(kani) file changed; ELF rebuild trigger did not fire. Historical
pins, not freshly reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No Rust, SBF, wallet/key operation, push, other worker prefix or live session-A
worktree was used. No binary/object/ELF is committed.

## Stop reason and next deliverable

Stopped on the checked arbitrary-instance counterexamples, not budget
exhaustion and not L160 removal. Concrete identification remains possible
but unproved. The next deliverable is a SPECIFIED concrete Implementation
constructor on CPhy's exact SDK and SolanaDigest, with proved CurrentCaller /
VTop carrier transport, operation return AND ordered oracle-effect laws,
and the AuS1 finish branch. Specialize the endpoint to that constructor;
retain L157/L159 and D188/P6 unchanged. The new constructor cannot be replaced
by a compatibility premise or by an assertion that every typed Implementation
is already the installation.
