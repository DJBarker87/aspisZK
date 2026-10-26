# F3K continuation handoff — budget exhausted

UNADOPTED frozen3 CANDIDATE. Owner option-B decision pending. S2 OPEN.
**Target not yet established.** No `F3K_Join.accepted_log_eq` theorem, composed
join non-vacuity proof, or checked impossibility witness has been established.
Stopped at the authorized 100/100 actual Lean invocations; zero Kani runs.

## Established claims

- `F3K_QueryFull.exact_row`: complete concrete source query call equals literal
  row31's observed log, ordered query output and selected state. The eight
  source squeeze/advance pairs, LE words, mask, decoder updates and stopping
  cases are proved individually; no desired log equality is assumed.
- `F3K_InactivePhysical.row`: the row28 physical frame follows from actual
  source parsing/serialization, including the inactive wide value encoding.
- `F3K_OpeningSuffix.sampler`: six source calls at rows27–32 compose in order;
  model final state equals decoded source rho state. Uses source calls, frame
  equalities, backend and incoming prefix/state premises.
- `F3K_NativeQuery33.native`: from one accepted original native pair, constructs
  the same source cuts/recorded trace and a model input whose complete33 sampler
  log equals source initialization + first25 calls + two actual circle Code
  logs + reseed + six source opening/query/rho calls. Also supplies exact source
  query coordinates and the source final transcript state.
- `F3K_NativeProtocol33.native`: identifies the sampler composition with actual
  LiteralByteProtocol chain log and final transcript projection on that pair.
- `F3K_OuterPrepareSplice.reached`: exact outer source preparation log splits
  into successful semantic child and successful closed preparation child logs.
- `F3K_PrepareLog.spine`: exact source opening preparation log consists of its
  actual reseed and the six calls. `F3K_OpeningSpine.from_double` constructs its
  source spine from the actual source double-stage success.
- `F3K_PreparedSourceFields.fields`: source Prepared fields equal the successful
  source spine's values. `F3K_CheckpointPreparedFields` transports variant,
  source query decoding/bounds and final state through the actual writer maps.
  `F3K_CheckpointQuerySource.source` proves the numeric checkpoint query function
  equals the strict source query decode, coordinate by coordinate.
- `F3K_InputFinalState.fields` and `F3K_ContextFinalState.input` identify the final
  model context state, conditional on successful model input discovery and33
  rounds. They do not prove that discovery succeeds.

Exact statements and retained assumptions are in `lean/F3K_*.lean`; source
hashes and matching successful snapshots are in `F3K_FINAL_SOURCES.json`.

## Assumptions and trust boundary

Native theorems retain the installed adapter/ops, query/geometry/finish/std
boundaries, AeneasExtraction, two actual native acceptance equations, P1 and
RuntimeSyscall. The original arbitrary ghost words `w` remain explicit; they
are not reconstructed from source/model arithmetic. The same native pair is
obtained once through RawJ_RecordCuts.native. No separate local fixture is
substituted for it and no model acceptance assumption is added to those sampler
construction theorems. Local source lemmas retain their explicitly stated
source successes, backend, frames, length bounds and source spine premises.
No protocol, security contract, probability assumptions or model definitions
were changed. Whole Prepared equality and input discovery are not discharged.

## Remaining obligations and next concrete deliverable

1. Identify the successful semantic child Code log with initialization,
   first25 and the two source circle logs, then splice it and PrepareLog.spine
   into the original recorded GExq/full source log. Current NativeQuery33
   identifies the sampler-side list, not that list's full recorded-log position.
2. Reconstruct ghost words and prove model input discovery, arithmetic,
   challenge/data and complete Prepared equality. Source Prepared field
   identification alone does not identify model arithmetic values.
3. Prove source/model accumulator correspondence, actual saved/resumed complete
   checkpoint body/header bindings, unconditional checkpoint alignment, then
   batch0/batch1 and finish composition on the original pair.
4. Prove `F3K_Join.accepted_log_eq` at the existing F3_JOIN-GATE exact carrier;
   establish non-vacuity of that composed join. No exact-carrier obstruction
   has been checked. Failure to finish is not evidence of impossibility.

The next deliverable is item1's semantic-child exact Code-log theorem and its
splice into the same RawJ recorded trace, consuming the named source successes
already exposed by OuterPrepareSplice.reached. Do not promote the current
sampler theorem to whole accepted-log equality.

## Validation and resource record

100 actual focused Lean invocations,61 exit0 and39 failed; no dependency builds,
no package/manifest replay and no Kani/Rust runs. Failed diagnostics are retained
and are not accepted evidence (some show Lean recovery `sorryAx`). Every final
source has a matching exit0 receipt. `F3K_Audit.lean` imports all60 substantive
modules and audits all89 named theorems once. It passed at attempt100:

- Command: `lake env lean -j1 -M7000 -DElab.async=false -o F3K_Audit.olean F3K_Audit.lean`
- Source revision: `741d5265c2f37ee22b6d91f93becaedc48012ed0` plus hashed new audit.
- Exit0; wall2.0757091020350344s; peak RSS5242344KiB; swaps0.
- Axioms: subsets of propext, Classical.choice, Quot.sound only.
- Own systemd scope: f3k-100; MemoryHigh6G, MemoryMax8G,
  MemorySwapMax0, TasksMax64. Each earlier actual run has the same limits.
- All attempts combined:327.6186485188082s measured command wall time;
  largest RSS7169832KiB (failed054); swaps0. Exact per-target records, commands,
  source revisions/hashes, dependency fingerprints, limits and axioms are in
  F3K_ATTEMPTS.jsonl and individual receipt/time/stdout/source directories.

Attempt054 hit Lean's -M7000 kernel memory limit; it was replaced by symbolic
one/pair/four/six-row composition, not rerun unchanged at a higher limit.
All final sources pass static forbidden-proof/option checks and git diff --check.
Final host scope inventory showed no running F3K scope; other workers' Pool
scopes were left untouched. Reused pinned coherent SInt2 objects including
F3_/F3J_/RawJ_/RawK_/LogA_ and their transitive caches. Focused imports against
these caches are not a coherent release rebuild.

## Frozen target and artifacts (AGENTS section6)

Branch: codex/cx-frozen3-join2-20261026. New F3K modules only; all receipts in
this directory. Parameters, features and wire format inherited unchanged from
the frozen3/F3J handoff and imported frozen sources; this work claims no new
release target. Toolchain Lean4.32.0; binary and dependency hashes are in receipts.
No shipped files, cfg(kani) harnesses, Rust source, ELFs, wallets or keys changed.
Consequently no three-ELF rebuild was triggered. Existing artifact pins are
inherited and were not reproduced or newly certified:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No frozen2 or existing headline edits; no session-A worktree or foreign-prefix
candidate changes. Stage commits are local only. No push. These results do not
establish release soundness, extraction, privacy, or a concrete security level.
