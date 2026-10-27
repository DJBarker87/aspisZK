# Joint fixture22 handoff

S2 OPEN; the deployed 100-bit target is not yet established. Branch
`codex/cx-joint-fixture22-20261027`, base
`42b19456a512350264ecf02f98a5d257adc702ac`.
Only new JGn-prefixed Lean modules and this receipt directory changed.
No push, merge, shipped-source change, session A worktree/candidate change,
wallet/key operation, Rust/Kani/SBF build or package/manifest replay occurred.

## Kernel result and exact boundary

**Ordered deliverables 1 and 2 are proved. Deliverables 3–5 remain incomplete.**

- `JGn_TerminalIdentified.identified` (087) is a CLOSED kernel proof of the
  UNCHANGED `JGe_TerminalCondition.Identified` guard:

  ```lean
  FIq_Terminal.terminal JFs_PublicSerialization.value JFu_ClaimsData.claims
    JFm_PartialAlpha.a10 JFm_Begin.challenges =
      ok (.Ok JGd_NumericData.neededTerminal)
  ```

  The return limbs are1711374173,2026192144,428817833,318295749. The generic
  `source` theorem has no Prop premises and works for every supplied dictionary/
  hash. The closed theorem instantiates a mathematical SHA256 dictionary on
  Unit, with the ordinary identity copy operation. It introduces no successful
  verifier callback, replacement operand, oracle-seed equation or new axiom.
- `JGn_MaskedAcceptance.source` (088) jointly constructs that actual terminal
  call, the original mask call and the actual masked arithmetic run returning
  JGd's final running value. `JGb_MaskedArithmetic.run` includes the ORIGINAL
  `Array.index_usize JFu_ClaimsData.a3 28#usize`; the imported `read` theorem
  identifies its return with q115. `JGn_MaskedAcceptance.formula` proves
  mask + eta*terminal + q115 = final running value, unconditionally.
- `JGn_CurrentPreparation.inhabited` (089) removes the terminal-identification
  Prop from the exact existing current semantic/originalNew fixture. The
  original shared witnesses, quantifiers, carriers and conclusions are retained.
  It is NOT a theorem of enclosing `candidate.prepare`.
- `JGn_SplitSource.source` (098) proves the original mutable-split procedure's
  complete symbolic return and valid/invalid-length back-function behavior.
  `JGn_PrepareBuffer.split/recombine` (099) instantiate it on the actual14759
  zero-byte scratch buffer, with the retained13831-byte semantic and928-byte
  Y1 initial slices. This proves the precise buffer lens, not allocation.

No `JGn_TX1.accepted1`, actual writer/checkpoint equality or complete
`JGn_Fixture.inhabited` is asserted. No genuinely unequal real-byte operand
or impossibility/vacuity counterexample was found. A failed elaboration,
heartbeat limit or missing source proof is not a vacuity finding.

## Source coupling and proof strategy

JGl's public-initialised real-byte fixture and all existing source VALUE
refinements are imported read-only. No retained vector or generic source law
is re-proved. New numeric word certificates establish the complete leading and
interpolated-full packed returns (`JGn_LeadingNumeric`, `JGn_FullNumeric`),
all four Native07 residuals (`JGn_PoseidonNumeric`), all14 original compressed
patterns (`JGn_CopyPatterns.source`), every slot of all four arrays through
all136 copy links (`JGn_CopyFold.value`), and the actual active selector and
copy residual (`JGn_ActiveNumeric`, `JGn_CopyNumeric`).

`JGn_CompositionValue.value` inverts ONE original successful composition,
identifies its original gathers/selectors/children, and uses THAT prepared
multiplier, both original iterators and both original Horner calls. It does
not transfer a value from an independently chosen successful child.
`JGn_SelectedHelper.value` identifies H1 by the SAME gather/read and checked
source index arithmetic. The terminal proof consumes that same composition
and original terminal continuation, then uses canonical decode injectivity.

All field arithmetic is reduced to small word certificates through imported
word-tower lemmas. Named vector phases, eight-link row chunks, short Horner
cuts and equality-weight cuts prevent normalization of large field towers.
Generators and their `--check` modes are retained. Uncompiled alternatives
are `.txt` files under `JGn_UNCHECKED`, with no proof credit.

## Exact remaining obstruction and next deliverable

`JGn_TX1Prefix.inhabited` (100, declared in `JGn_FinalAudit.lean`) also removes
Identified from JGi's unchanged SAME-byte WAdm readiness theorem. It supplies
ONE current semantic/originalNew witness and the original entry's exact
`afterScan` continuation identity. Its statement explicitly does not assert
that continuation succeeds.

The first unfinished source body is `verifier.candidate.prepare`. Complete
its actual14759-byte allocation and metadata-slot binding, then use the checked
split/recombine lens and the existing actual expansion/view/semantic/new
returns to construct the WHOLE prepare call. The inspected installation
retains base allocation op1 and layout slots op12/13/14/15. The real geometry
is logical semantic13831, logical Y1928, total14759, semantic offset16,
stored semantic7015, Y1 offset7031, stored Y1464, inactive offset7495.
These actual base operations still need their concrete installation instance;
no whole prepare success is added as a fixture hypothesis.

Then consume the SAME prepared value/scratch in Tx1Q's batch0, geometry,
pending and query0–9 calls, flush and WAdm writer. Construct actual accepted1,
and prove the RETURNED writer Vec's bytes equal the retained1768-byte
`JFx_NativeBytes.checkpoint`. Defining `JFv_World.saved` from those bytes is
not that equality and is not used as its proof here. Join actual TX2, frozen3's
SAME pair, the approved game/RuntimePersistence/admission instance and the
adopted ARX root only after those calls are inhabited.

### TX2 conjuncts open in this branch

No claim is made about the parallel JGm worker's unmerged results. At
`pub := JFx_NativeBytes.publicInput`, `proof := JFx_NativeBytes.proof`,
`checkpoint := JFx_NativeBytes.checkpoint`, reserved=true and the SAME actual
installed D/queryOps/finish/hash, the shared existential output conjuncts of
`Tx2N_Twelve.accepted` remain exactly:

```lean
Port4A_ReaderInstall.reader reserved D checkpoint proof pub .S2 hash =
  ok (.Ok (p,saved))
Port3_QueryStage.query (Port4C_RowStd.install (Port5Q1_QueryPorts.install queryOps))
  proof p saved g none geometry pending 22#usize = ok (.Ok (returned,after))
alloc.vec.Vec.deref_mut returned.weights = (returned.weights.deref,back)
Port3_FlushInstall.flush after returned.weights.deref = ok flushed
Port4D_FinishInstall.finish finish v p {returned with weights := back flushed}
  none = ok (.Ok ())
```

The p/saved/g/geometry/pending/returned/after/flushed/back/v are outputs from
ONE source run, not independently supplied successes. The original complete
success observation remains:

```lean
VTop_Stages.verifier.candidate.tx2_authenticated
  (Tx2I_Install.stage (Tx2N_Execution.control base reserved queryOps geoOps) finish)
  D pub proof checkpoint hash none = ok (.Ok ())
```

The SAME savedVec must satisfy actual TX1 writer equality and
`bytesOf checkpoint.val = bytesOf savedVec.val`. The saved-ten/twelve-advance
relations and actual T2Nat/FinT source cuts, round/pair/dot/final-rhs relations
and indexed packed recovery bindings are uninstantiated here. The adopted
root's deployment observations also remain uninhabited:

```lean
S2W_D189Wrappers.first native1 copy allocator e1 CPH_Program.verifier data1 state1 =
  ok (.Ok (saved,post1,final1))
S2W_D189Wrappers.second native2 allocator e2 CPH_Program.verifier data2 slot state2 =
  ok (.Ok (post2,final2))
```

## Before/after, ledger and non-vacuity

The actual adopted target is `AspisR1.ARX_Root.deployed`. Its complete
BEFORE/AFTER source statements are BYTE-IDENTICAL in
`JGn_BEFORE_ARX_Root.lean.txt` and `JGn_AFTER_ARX_Root.lean.txt`.
The BEFORE kernel print is explicitly reused from JGl; the AFTER kernel print
is fresh from100. The host ARX source matches this branch exactly, SHA256
`f3292a045b924fda8e23f13704d4fdbb6bdd73b3665c3abf0ad0f77025435405`.
No pre-existing source definition is edited.

Ledger method: quantified atomic law families/conjunction leaves, preserving
shared witnesses, dictionaries, guards, quantifiers, failure events and
all deployment rows; retired aliases such as L185 are excluded. The owner-
approved post-L166 baseline remains BEFORE=AFTER:

- actual:83T/11P/13G/0C;
- deployment-inclusive:89T/27P/13G/0C;
- removed, added and changed:0T/0P/0G/0C.

The local Identified premise is genuinely removed from the unchanged current
preparation and SAME-byte WAdm readiness statements by applying its CLOSED
proof. Full local before/after statements and fresh AFTER kernel prints are
retained. This earns NO adopted-root premise-removal credit. No security
hypothesis, trust item, carrier, quantifier, metric, constant or conclusion of
the adopted root changes. The approved frozen3/game/RuntimePersistence scope
is retained.

Non-vacuity established: the actual retained real-byte native terminal has
the required canonical return; the original masked arithmetic accepts it;
the actual semantic/originalNew preparation and SAME installed WAdm entry
prefix have witnesses without a terminal-success hypothesis. The buffer lens
is also proved on its concrete scratch bytes. This is NOT accepted-wrapper,
writer/checkpoint byte-identity, SAME accepted pair or deployed non-vacuity.
No actual real-byte contradiction was established.

## Validation and resource record

**Budget exhausted:100/100 charged attempts;99 Lean processes,74 accepted and25
rejected, plus075's missing-predecessor launcher preflight;0/10 Kani. No further
Lean/Kani run is launched.** Failed recovery sorryAx output is retained and
excluded from all claims. All63 final Lean module sources match accepted
receipt hashes (`JGn_VALIDATION.json`, `JGn_FINAL_SOURCES.json`). Uncompiled
alternatives are excluded from the import tree.

`JGn_FinalAudit` (100) succeeds after65 selected cached prerequisite objects
were checked present, with exact new-module and adopted-root source hashes
matching the host. It imports all62 completed new component modules, imports
JGl's final closure, proves the guard-free SAME-byte prefix consumer, freshly
prints335 component theorem audits, that new prefix theorem and the adopted
root. All337 reports use only propext/Classical.choice/Quot.sound or subsets.
The root report is exactly:

```text
'AspisR1.ARX_Root.deployed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exact final target/command:

```text
JGn_FinalAudit.lean
/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake env lean -j1 -M7000 -DElab.async=false -o JGn_FinalAudit.olean JGn_FinalAudit.lean
```

100: exit0; wall6.341176315967459s; peak RSS6246088KiB; swaps0;
source revision`1f01b45167a0e65a2bdc2807611bc95ba0ad239c` with the new audit
source dirty; exact audit source SHA256
`c9988ccc447481af5b58358d8b6772100ddd453f5ea708959644502f4a665e94`.
Full per-theorem axiom lines, source hashes, selected dependency fingerprints,
limits and command are in `JGn_RESOURCE_AND_AXIOMS.json` and the100 receipt.
Total Lean wall1102.6017986297375s; maximum RSS6246088KiB; swaps0.

Every Lean process used the unchanged S2W host launcher in its own systemd
scope, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64, -j1/-M7000 and
asynchronous elaboration disabled. No cap was raised. Exactly one Lean process
ran at a time. 069/074 reservation contention was handled by the prescribed
180-second retries. Every admission wrote its host barrier log before scp.
075 was scheduled while074 was still waiting; its launcher correctly rejected
the absent JGn_ActiveNumeric object before Lean. It is charged and retained
with N/A Lean wall/RSS/swap/axioms. No infrastructure was changed.

036's full power graph and069's unguarded fold comparison hit default
heartbeats;095's concrete split rewrite hit default recursion depth. None was
rerun unchanged or with larger limits. Replacements are named short power
prefixes, a guarded fold-layout bridge, and a generic symbolic split law
followed by its concrete consumer. Their failed snapshots and replacements
are retained. No memory-killed process occurred.

The coherent SInt2 host workspace and its retained objects were reused:
`/home/dombarker/project-offloads/codex-cx-sound-int2-20261025`.
The pinned d18v5 circle cache precedes the retired aggregate in LEAN_PATH.
`JGn_FINAL_OBJECT_PINS.json` records all63 new objects and the adopted root,
including exact object/source hashes and sizes. `JGn_SCOPE_CLOSED.json` confirms
all99 Lean scopes and075's launcher-only scope are unpopulated or removed.
Every source/command/revision/dependency/exit/wall/RSS/swap/axiom receipt is in
`JGn_ATTEMPTS.jsonl` and `JGn_RECORDS_MANIFEST.json`. This is a focused coherent
cached-object audit, NOT a fresh frozen-release rebuild.

No second corpus/workspace, cargo target or solver temp files were created.
The coherent proof cache is retained for the next consumer; it is not disposable
compiled scratch. No binary, object, tarball, ELF or key is committed.
Generator checks and final source/forbidden-token/whitespace checks pass.

No shipped source changed, so no ELF rebuild was triggered. Inherited pins,
NOT freshly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

All stage commits remain local; no push. The complete accepted fixture and
the deployed100-bit target remain not yet established.

The proof/source/document diff check is clean. The unrestricted git whitespace
check reports original whitespace in raw tool/driver logs only; those logs are
retained byte-for-byte rather than edited (`JGn_RAW_LOG_WHITESPACE.json`).
`JGn_STAGE_COMMITS.txt` lists the seven stage commits preceding the final audit/
evidence commit. Source revision100 and every source snapshot remain exact.
