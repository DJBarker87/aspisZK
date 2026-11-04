# D598 — RuntimeReturnData and privacy

**Answer: NO.** No consuming privacy definition, theorem or ledger row was found at the revisions below. The Pool's authenticated dispatch uses this runtime property, but the inspected privacy statements do not assert that its verifier verdict reaches the Pool unchanged. Settlement acceptance/rejection, verdict bytes and logs belong to the public observation contract. Their complete deployed representation and simulation remain obligations; absence of a return-data dependency does not close those obligations or establish privacy.

## Scope and immutable sources

Read-only source/statement research on `codex/pv-scout-20261104`, exactly `/Users/dominic/ZK/.worktrees/pv-scout`, sparse configuration preserved. Starting HEAD `57aa1b9dd3ce05e58d22db09ca9b0681cac9ef22` (H).

| Label | Branch | Inspected revision |
|---|---|---|
| RW | codex/cx-prover-rw-20261023 | 8e450dab55887ad4481fc600a4b0551645725296 |
| EVH | codex/pv-evh-20261029 | fd4a644fd414079022f8781c14a6683b41504ab7 |
| RJ | codex/pv-runjoin-20261026 | 100d9075d2fcd8adbde84cd548a0e42e55df93ce |
| MEAS | codex/pv-meas-20261029 | ba1fa07d9e2dcf54155793bee1d6ae2784c0b1c6 |
| RC11 | codex/pv-recount11-20261104 | e5aabf4de13297450fc1e69206d09b8150eab95f |

References below are `revision:path:line` (line numbers from `git show ... | nl -ba`). Let `R1Z/` mean `docs/research/v8-r0-zk-20261009/lean/R1Z/` `R0Z/` mean `docs/research/v8-r0-zk-20261009/lean/R0Z/`, and `LOG` mean `docs/research/v8-r0-zk-20261009/LOG.md`. No sources or objects were imported from another worktree.

The ruling supplied in D598 is recorded verbatim, as context rather than an independently verified runtime theorem:

> set_return_data(b) by program P, read by the immediate caller's get_return_data() with no intervening CPI, returns Some((P, b))

Stream A labels it `RuntimeReturnData`, ruling (ab), C3-BIN 2026-11-04. Actual Pool use: H:`programs/aspis-pool/src/verifier_dispatch.rs:145` delegates the read to the runtime; `:308` requires an immediate unchanged snapshot; `:377–384` clears, invokes, reads, rejects missing data and authenticates the returned program/bytes. These are implementation consumers, not privacy consumers.

## Candidate consumer audit

| Definition/theorem/row inspected | Exact source | Finding |
|---|---|---|
| `PrivacyR1HeadlineDeployedReal.RustRealRefinement`, `privacy_headline_deployed` | H:`R1Z/PrivacyR1HeadlineDeployedReal.lean:56`, `:69`, `:80` | Abstract `FSExperiments`, observer program and joint RunJoin of ROMView/decision. No CPI, return-data or verifier-to-Pool equality. |
| `PrivacyR1HeadlineDeployedEvents.Runtime`, `Links`, `privacy_headline_deployed_events` | EVH:`lean/PV_EVH_Deployed.lean:75`, `:181`, `:223` | Native trace/signal are parameters. Links concern publication, diagnostics, counts/time/oracle/retained channels, coupling, context, signal, environment and observer. None specifies return-data delivery. |
| Measured `Runtime`, `Links`, `privacy_headline_deployed_events_meas` | MEAS:`lean/PV_MEAS_Deployed.lean:81`, `:219`, `:272` | Same observation mechanism with probability laws, measurable decisions and conditional-law obligations (`:167–209`). No new settlement mechanism premise. |
| Adaptive `Observer`, `completed`, `observer`, `ideal`, `real` | EVH:`lean/PV_EVH_Core.lean:66`, `:73`, `:79`, `:91`, `:100` | Both queries and decisions see Signal × Observation; ideal uses unchanged simE and public completion. Native observations survive failures. No verdict forwarding law. |
| `Observation`, `NativeEvent`, `nativeObservation` | EVH:`lean/PV_RJ4IDB_Decoder.lean:4`; `lean/PV_RJ4IDB_NativeTrace.lean:7`; `lean/PV_RJ4IDB_NativeFactor.lean:7` | Ordered bytes, terminal, files, diagnostics, counts, timing, oracle/rejections and retained named payloads. Generic carriers can represent settlement; they do not themselves identify actual settlement/log events or prove their acquisition. |
| `Signal`, `attempt`, `run` | RJ:`R1Z/PV_RunJoin_EffectClient.lean:21`, `:37`, `:64` | `.published` is a produced proof plus attempt index. `.rejected` is a prover body error used for retries. Neither is Pool acceptance. |
| Option-B `Link_PublicSignal`, `V400`, deployed independence | EVH:`lean/PV_EVH_Residual.lean:55`; `lean/PV_EVH_Deployed.lean:155`; RJ:`R1Z/PV_OptB_DeployedSignal.lean:17` | Witness-independent failure-signal law, retaining prior events, with explicit native synchronization hypotheses. No assumption that CPI succeeds or returns an unchanged verdict. |
| `RUNJOIN_PUBLISH_COMPACT`, `RUNJOIN_STATEMENT_BYTES` | RJ:`lean/PV_RJ4IDB_OpenInputs.lean:11`, `:15` | Equality to serialized proof/publication and statement bytes, not publication of verifier return data. `PublicationInput` at RJ:`lean/PV_RJ4IDB_Publication.lean:6` contains afterstate, compact proof, statement and output paths. |
| Latest publication `Remaining`, `publication` | RJ:`R1Z/PV_RunJoin_NativeFinishDischarge69.lean:12`, `:30` | Seven sampler/backend/query/node/order links feed the same compact-proof equation. No Pool/return-data link. |
| Historical deployed `Runtime`, `rust`, `PV_RunJoin_Premises` | RJ:`R1Z/PV_RunJoin_Deployed.lean:23`, `:51`; `R1Z/PV_RunJoin_Endpoint.lean:76`, `:103–110` | Disclosure/oracle equality is explicit; actual observation interpretation remains to be supplied. No unchanged-verdict requirement. |
| Capped trust `PV_RunJoin_TrustItems.observation` | RJ:`R1Z/PV_RunJoin_TrustItems.lean:34–52`, `:64–74` | Equality of native/extracted ordered world calls, filesystem and complete payload. Its statement contains no return-data axiom or concrete Pool interpretation. Do not infer the runtime property from this abstract equality or silently fold it into T. |

## Settlement, D159 and ledger interpretation

The D159 observer must see settlement accept/reject, the public verdict and published logs/errors, as well as counts/timing and other retained effects. This is an observation requirement, not a claim that settlement equals a particular verifier Boolean. H:`LOG:8436–8460` sets L1/L2/L3 coverage. H:`LOG:13132–13154` (D348) explicitly includes on-chain logs/error bytes and proposes simulation from public transaction bytes plus the public execution context actually read.

The historical coverage gap is explicit at H:`evidence/privacy-recount-20261026/recount7/D348.md:6–32`: abstract Aux could encode logs, but no selected total reached-path association does so. `RustRealRefinement` does not repair that by naming a complete model view. H:`R0Z/ZkStatement.lean:37–57` has older `PublicOutputs.lifecycleEvents` and success/abort `outcome`; this older carrier is not evidence that the R1 endpoint represents deployed settlement or logs. The new event interface retains arbitrary named side payloads and terminals, but still needs the actual native producers and completion links. It contains no dedicated Pool-verdict identity theorem.

Ledger audit (H:`design/PRIVACY-LEDGER-20261026.md`):

- **V038** (`:88`): complete ROMView and observer-decision agreement on the same good sample; **V036/V037** are its coupling marginals. These are observation/refinement obligations, not a return-data law (`:478–486`).
- **V347–V351** (`:412–416`): native ordered L1 events, joint count/TLS/oracle law, exception/abort integration and composition. **V352–V369** (`:417–434`) cover L2 native trace/branch/index/cost laws and joint raw inputs. None asserts unchanged verdict transport. An observation change can affect these open associations; that is not evidence that they consume Stream A's exact axiom.
- **V406** (`:826`, `:964–972`): capped three-field T, including abstract native/extracted observation. No fourth runtime-return-data field.
- **Recount 10** (`:2096–2114`): measured Signal×Observation and all original runtime fields retained; publication links reduced to seven; native L1/L2 associations remain open. `:2152–2155` retains actual event acquisition/joint D163/D166/V400 and final release obligations.
- **Recount 11 available snapshot:** RC11 ledger still ends with recount10 at `:2155`; there is no completed recount11 row table at this pin. RC11:`evidence/privacy-recount-20261026/recount11/METHOD11.md:13–35` explicitly retains all407 inherited rows, separately reports event/measured endpoints and preserves full D159/capped T. Its `rederive11.py:7`, `:20` retains native observation/RunJoin obligations, including V038. This is work-in-progress evidence, not a completed recount11 verdict.

Thus the model takes observable settlement as part of the public transcript to be represented/simulated, without depending on *this particular transport mechanism*. Public does not mean constant or automatically simulatable: actual settlement/log/context and joint failure/timing laws still require association. This finding does not show privacy for an arbitrary faulty runtime that leaks secrets.

## Recommendation and validation

**No new privacy trust item is needed for RuntimeReturnData.** Retain Stream A's exact row on its soundness/runtime path. Do not duplicate it in privacy T merely because verifier dispatch is deployed: no inspected privacy premise consumes correct unchanged verdict delivery. Keep the existing full-observation, native event and settlement/log coverage obligations explicit. If a future concrete privacy completion proves settlement by identifying the Pool result with the emitted verifier result, that new proof must cite the exact runtime row above and be reviewed before credit; no such proof is present here.

Validation was source inspection only: `git show`, `git grep`, `git ls-tree`, `rg`, branch/status checks. Searches covered the three requested branch tips in `R1Z/*.lean`, `lean/*.lean`, and privacy design files for `RuntimeReturnData|return_data|emit_result|verifier_dispatch`, plus settlement/verdict/on-chain terms; measured sources were inspected separately. At each immutable RW/EVH/RJ/MEAS pin, `git grep -n -E 'RuntimeReturnData|return_data|emit_result|verifier_dispatch' <pin> -- 'docs/research/v8-r0-zk-20261009/lean/R1Z/*.lean' 'lean/PV_*.lean'` found zero hits (exit1, the normal no-match status). Broad `lean/` search on RW found Stream A files (`JHb_Emit`, `NDO_JHb_Emit`, `NBX_FrameComposition` and audits), which are not evidence of a privacy consumer; event/measured/publication statements above do not invoke them. No Lean/native/Kani/build/host runs, axioms audit or runtime verification was performed. No premise removed, added or weakened (0/0/0); no measurement or new proof claimed. Only this evidence directory was edited; no Stream A edit, key operation, merge or push. Privacy target remains not established.
