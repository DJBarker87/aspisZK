# NOF slot audit: residual (seed) slots on the installed TX2 path

Ordered by the lead before P2. Scope NOF_L005 (stage AUDIT, 1 of 2 allowed), exit 0,
wall 25.4 s, peak RSS 6826500 KiB, swaps 0. Raw output: NOF_SLOT_AUDIT_RAW.txt.

## Method

`NOF_SlotAudit` defines the installed stage and SDK as functions of the residual seed
`m : IDa_Deployed.Uninstalled _` (`stageF m env err r := NNH_Tx2SlotTransport.stage m env err r`,
`sdkF m env err r := NNH_CorrectConfiguration.sdk m env err r`) and, in MetaM, puts every
field of `VTop_Stages.Ops` (24 + unwrap32) and `AdapterRw.Ops` (54) into weak-head normal
form with `m` a free variable. A slot is **residual** iff its whnf is (after stripping
lambdas) a projection chain rooted at `m`; in the literal host seed `NNH_HostSeed.m0`
exactly those slots are the `.div` placeholders. `mentions_m` is a coarser flag (the
installed body mentions `m` somewhere, e.g. through the configuration record).

Reached adapter slots of `stage2_owned` were enumerated by a transitive crawl of the
AdapterRwModel source (call chain per slot recorded below).

## Result: no reached slot is a residual

Top-level residual slots: **only AdapterRw.op21 and AdapterRw.op24**. Neither is called
by `stage2_owned` or anything it reaches. All 25 stage slots are non-residual.

### verifier.candidate.tx2_common (stage = NNH_Tx2SlotTransport.stage m env err r)

| slot | call site | installation confirmed by |
|---|---|---|
| op18 resume | first bind | audit non-residual (head Port4A_ReaderInstall.reader); NNH_AuthResumeSdk.produce / NNH_ResumeOkPort.value (defeq to reader env.reservation; NNH_Tx2Configuration.reserved rfl) |
| op16, op14, op15, op20, op21, op22, op23 | constants | NNH_Tx2LiteralSlots.constants (rfl, all m) |
| op17 powers | after resume | NNH_Tx2LiteralSlots.powers (rfl) = Tx2N_Powers.powers |
| op13 mark | two marks | NNH_Tx2LiteralSlots.mark (rfl) = NHV_ReleaseOps.mark |
| op2 inactive | inactive slice | audit: non-residual, m-free (installed by NNH_Tx2SourceConfiguration.stage := NJC_ClosedCalls.inactive) |
| op0 ok_or | after inactive | audit: non-residual, m-free (head Port1_LibrarySource.okOr; NHT_Tx2CommonModel.constants) |
| unwrap32 | folded root | audit: non-residual, m-free (Port4B_FoldedCut.unwrap32, AuS1_Install.base) |
| op5 Merkle | folded root | NNU_MerkleSlots.installed (all m) = Port4B_Install.batch |
| op11 geometry | after Merkle | NNH_Tx2SlotTransport.geometry_slot (rfl); NNU_Geometry.source (all args) |
| op10 pending | after geometry | NNH_Tx2LiteralSlots.pending (rfl) = Port3_NativePendingInstall.source env.reservation |
| op6 query | after pending | NNU_Query.source (equal to NJJ_Common.query on the reached Domain/next/powers/pending) |
| op9 flush | tail | NNH_Tx2LiteralSlots.flush (rfl) |
| op19 finish | tail, obs = none only | NNH_Tx2SlotTransport.finish_slot (rfl); NNH_ResultPortTransport.finish |

op6/op10/op11/op18/op19 carry `mentions_m=true` (they close over the configuration record),
but each is equated to an m-free installer by the compiled theorems listed. op6 is equated
only on the reached domain; off that domain it is not used by any A2 statement.

### stage2_owned / sdk entry (sdk = NNH_CorrectConfiguration.sdk m env err r)

op11 (TX2 entry) = `verifier.candidate.tx2_authenticated (stage …)`: non-residual; reaches
stage op3 (parser; non-residual, m-free; NNY_ParserAssociation.source) and the tx2_common
slots above. op44, op53, op19, op22, op2–op9, op13–op20, op23, op25–op41, op45, op46,
op48–op53: all non-residual. op12 (`require_verifier_checkpoint`) has head
`NGL_CheckpointModel.install.match_1`; its non-S2 branch falls back to the residual
`m.adapter.op12`, but the only call site passes the literal
`aspis_r1_cost_probe.transport.Variant.S2`, which takes the installed branch `ok 1768#usize`.
op10/op42/op43 appear only under `observer → first_decoded`; `AdapterRw.Cuts.observer_none`
(`observer ops = ok none`, rfl for every ops) shows `first_decoded` is never invoked there.
op10 is the only reached-by-text slot that mentions currentBase (head
AspisS6CurrentFirstInstallation.current), and it is unreachable for that reason.

## Consequence for NOF theorems

No divergent slot is reached on the TX2 path; P2 proceeds. Every NOF theorem quantifies
over an arbitrary `m : IDa_Deployed.Uninstalled _` and never mentions `currentBase`
(in particular not `currentBase.op1`), so each stays valid when the seed's current-caller
op1 is corrected.
