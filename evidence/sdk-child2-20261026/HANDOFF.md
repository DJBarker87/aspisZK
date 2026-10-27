# SdkD handoff — budget exhausted, full closure incomplete

Branch: codex/cx-sdk-child2-20261026. Worktree: cx-sdk-child2. Prefix: SdkD_.
Receipts: evidence/sdk-child2-20261026. No push, no shipped changes.
100 charged Lean attempts used (including missing unchanged dependencies),
0/30 Kani. Stop reason is the explicit compile budget. No checked shipped
counterexample. The requested removal of BOTH premises is NOT achieved.

## Checked top and exact before/after scope

Before: Uni_Accepted.accepted_pair_unified takes arbitrary E,
port : ChildConeJoin E sdk, firstMarks and secondMarks. The Tx2N theorem
separately returns Outcome, whose inner continuation takes

    authenticated_S1 : ∀ pos, pos < 22 → recovered (index q 2 pos) =
      some (payload ⟨bytesOf proof.val,semantic⟩ 2 pos)

After: lean/SdkD_Accepted.lean, accepted_pair_unified (023), retains ALL Uni
conclusions and adds Tx2N_Finish.Outcome on exactly the SAME f,s,cuts and
checkpoint history witness. E/port/marks are absent as caller inputs. Its
result uses let port := SdkD_Child.port ..., with E=Unit. TX2's stage dictionary
is specialized to Tx2N_Execution.control as in Tx2N. No new trust item or
compatibility/chosen-cut premise is introduced. The concrete child is a
source-computed SITE projection, with all-input erasure and actual-Ok guarded
marks, including arbitrary observer arguments. This is an explicit change
from arbitrary effect payload to a concrete site observer; it is not a global
digest-log/probability refinement. Outcome STILL contains authenticated_S1.
Thus the requested global source-associated child and authentication closure
are not established by naming this top SdkD_Accepted.

## Derived source provenance and indexed batches

Stages 3..5 derive these without assuming packed recovery or ten-step state
arithmetic:
- Installed preparation has variant S2, actual semantic parser roots, physical
  root slices16..48 and63..95, actual folded-root range7751..7783 and copy.
- Writer success exposes literal source byte construction; sparse root cells
  at112/144 and all22 little-endian query cells at320+4*j are symbolic proofs.
  Reader success recovers those same roots and the ENTIRE native22-word query
  array across equal checkpoint bytes, including differing proof/public inputs.
- Actual first/second batch paths are indexed by the same preparation/query
  map. Both successful partial-syscall checks transport to the canonical model.
- SdkD_ReplayPair.same_pair (073) takes ONE SourceCuts witness and obtains
  actual Tx1Q Run, then for SessionAPrepare on that returned run.p derives
  all six canonical batch checks via SdkD_BatchUnion. Repeated parents are
  covered by indexed paths; no deduplication or per-batch map is assumed.

ReplayPair uses SdkD_PairBatches.dictionary, which specializes the remaining
TX2 folded-root offset/unwrap slots using SdkD_Install.stage. It is NOT already
appended to the SdkD_Accepted result. The joint top can be specialized to those
slots using SdkD_Install.inner/commute; a follow-up composition must still
keep the SAME cuts and prepared witness. Do not claim that integration has
already been checked in a new top theorem.

## Preparation hash-source work

SdkD_PrepareLower (075) maps complete typed PreparedHashCode to the SDK Code;
its Program equality is structural. Its erasure needs a LOCAL Associated
law for each explicit native digest. SdkD_PrepareSource (099) instantiates the
complete immutable source tree on EXACTLY RowShape_InstalledSlots.verifierOps;
source/run_value hold for all outcomes, including rejection/fail/div and the
same returned gamma scratch. SdkD_PrepareTransport.accepted (100) proves exact
ordered result-and-log equality under actual source success, P1, partial
RuntimeSyscall AND that explicit Associated law. The association has NOT been
derived globally and is NOT added to SdkD_Accepted as a replacement premise.

The coherent host workspace is
/home/dombarker/project-offloads/codex-cx-sound-int2-20261025.
Reuse all SdkC_/SdkD_ objects and inherited LEAN_PATH from SdkD_100.json.
076..098 add 23 unchanged source dependencies through
S1CurrentPrepareCodeExactV1; SHA/size/path are in SdkD_host-object-manifest.json.
Immutable source copies are retained in each numbered receipt. Missing budget
dependencies now include S1PrepareBudgetCoreV1, S1PrepareBudgetTacticV1,
S1SemanticBudgetV1, S1PreparedBudgetV1, S1CurrentPrepareBudgetV1. Their sources
are already at evidence/port17release-20261024/dependency-source. Complete
preparation's existing structural budget theorem is 115 calls, but that is
NOT the instantiated whole SDK/adversary experiment Q.

## Ledger delta and security-bound accounting

| Row | Before | Checked delta | Status for full requested endpoint |
|---|---|---|---|
| L088 port.erasure | Arbitrary child binder | Concrete source SITE child/erasure supplied | Supplied for E=Unit site projection; full oracle child open |
| L089 firstMarks.source (Uni-corrected) | Actual-Ok guarded supplied marks | SdkD_Marks.first derives marks for literal source calls | Supplied locally and in joint top |
| L090 secondMarks.source (Uni-corrected) | Actual-Ok guarded supplied marks | SdkD_Marks.second derives marks for literal source calls | Supplied locally and in joint top |
| L164 combined installations | Uni already discharged | Preserve union, add Tx2N Outcome on same witnesses | No second row-removal credit |
| L157 canonicalJoin.verifier | Source oracle refinement open | Indexed batches and complete prepare tree advanced | OPEN |
| L159 StoredCarrierBinding | Full runtime experiment binding open | No global instance | OPEN |
| Tx2N Outcome authenticated_S1 (no new ledger ID allocated) | All22 indexed folded payloads assumed | Both source batches now imply canonical replay success | STILL PRESENT in joint top |

Globally removed rows: NONE claimed beyond the explicitly specialized
site-projection instance above. Added trust/premise rows in joint top: NONE.
The local Associated interface is a remaining proof obligation, not a trusted
assumption promoted into the endpoint. Other-cone obligations stay unchanged.
No global premise ledger or other-worker source was edited.

Exact added collision SECURITY-BOUND term from SdkC_Replay:

    6 * ((Q + 1040 : Nat) : Rat)^2 / (256^32 : Rat)
      = 6*(Q+1040)^2/2^256.

1040 is an explicitly charged appended canonical replay query bound, not
free verifier work. Q must count the WHOLE containing source/adversary
experiment. Source commitment-prefix extraction is unchanged by replay only
AFTER that actual commitment read (SdkC_Replay.cut_append). No extra
per-position or per-batch collision multiplier is needed by that theorem.
The global source experiment, uniform Q and actual original frame reads are
still uninstantiated. These are not disguised as security assumptions, and
no headline contract bound or 100-bit claim is established here.

## Non-vacuity and next obligations

SdkD_Nonvacuity.instance_exists (056) constructs the concrete site child and
both accepted-only marks for EVERY installed dictionary. Their removal
imposes no new acceptance restriction. This is not a proof that all remaining
runtime/crypto/other-cone hypotheses admit a complete accepted native pair.
No such joint fixture is claimed. The all-outcome source theorems and
success-conditioned oracle statements are distinguished explicitly.

To finish: derive complete concrete preparation Associated without total
syscall success, build the containing SDK/adversary Program BEFORE choosing H,
prove its global query budget including preparation/batches/checkpoint and
rejected prefixes, derive original root commitment-frame reads (folded root
row30 included), use SdkC_Replay.recover_or_collision on that SAME source log,
then instantiate one indexed recovered map for ALL22 folded payloads and
compose into Tx2N Outcome and the joint top. SessionAPrepare may remain the
named hypothesis. Do not replace these obligations by a bundled source
experiment premise and count that as removal.

## Verification and artifact pins

SdkD_final-audit.json maps all47 CURRENT prefix modules to successful exact
source snapshots, lists every charged attempt and its metrics/axioms, and
records70 successful/28 failed/1 stopped/1 prelaunch results. Each numbered
receipt includes full command, source SHA, selected object fingerprints,
revision anchor/dirty flag, exit, wall, RSS, swaps and axioms. 038 and074 have
explicit missing-metric explanations. Caps remained MemoryHigh6G,
MemoryMax8G,MemorySwapMax0,TasksMax64 with Lean -j1 -M7000. No package replay,
Rust gate, Kani run or frozen manifest replay was launched. Standard axioms
only for all checked new top theorems. Source forbidden-token and successful
axiom diagnostics were inspected; every added theorem has its #print axioms.

Inherited frozen pins (UNCHANGED, not newly rebuilt/revalidated here):
- default: f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet: 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool: 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No shipped or cfg(kani) file changed, so the conditional ELF rebuild trigger
did not apply. No keys were created/deleted/changed and no funds were touched.
No other worker's files/worktrees/candidates were modified. The release
security target and SECURITY-CONTRACT-20261021 remain unchanged.
